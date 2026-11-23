module Unbounded{
    import basicSpells.* from "./basicSpells"
    // number of processors
    pure val N = 3
    pure val QUORUM = N / 2 + 1
    pure val MAX_CRASHES = N - QUORUM

    // processors
    type ProcessorId = int
    pure val PROCESSORS: Set[ProcessorId] = 1.to(N)
    pure val WRITER = 1

    // message
    type Message = {kind: str, label: int}

    // Link
    type Link = (int, int)
    pure val LINKS = tuples(PROCESSORS, PROCESSORS)

    // Communicate
    // keeps track of procedure communicate of processor i accross steps
    type Communicate = {
        request: Message,
        // maintains status of communication between i and each processor
        status: int -> str,
        // maintains info from each processor
        info: int -> int,
        numAck: int
    }

    // state variables
    type State = {
        // maintains val_i for each processor
        val_i: int -> int,
        // maintains communicate procedure for each processor
        communicate: int -> Communicate,
        // maintains message for each link
        m: Link -> Message,
        // set of crashed servers
        crashed: Set[int]
    }
    var state: State

    // filler for no label entry
    pure val NO_INFO = -1
    // empty message
    pure val EMPTY = {kind: "empty", label: NO_INFO}
    // R1 message
    pure val R1 = {kind: "R1", label: NO_INFO}
    pure val INITIAL_STATUS = PROCESSORS.mapBy(_ => "notsent")
    pure val INITIAL_INFO = PROCESSORS.mapBy(_ => NO_INFO)
    // default communicate entries
    pure val IDLE = {request: EMPTY, status: INITIAL_STATUS, info: INITIAL_INFO, numAck: 0}

    // chooses highest of a and b
    pure def maxLabel(a: int, b: int): int = if (a >= b) a else b

    // check that m is a request
    pure def isRequest(m: Message): bool = Set("W ", "R1", "R2").contains(m.kind)

    // get ACK based on type of request
    pure def ackKind(m: Message): str =
        if (m.kind == "W") "ACK-W"
        else if (m.kind == "R1") "R1-VALUE"
        else "ACK-R2"

    // initialize
    action init = all{
        state' = {
            val_i: PROCESSORS.mapBy(_ => 0),
            communicate: PROCESSORS.mapBy(_ => IDLE),
            m: LINKS.mapBy(_ => EMPTY),
            crashed: Set()
        }
    }
    
    // turn: "my" before sending new messages and after receiving ack - when nothing in m
    def turn(link: Link): str =
        if (state.m.get(link) == EMPTY) "my" else "his"

    // i can start if i is not crashed and i's communicate is IDLE
    def canStart(i: int): bool = {
        not(state.crashed.contains(i)) and state.communicate.get(i).request == EMPTY
    }

    // i can write if it can start
    def canStartW(i: int): bool = canStart(i)

    // i can start R1 if it can start
    def canStartR1(i: int): bool = canStart(i)

    // initialize a communicate procedure for i
    def beginCommunicate(i: int, m: Message): State = {
        // reset status to all j to notsent, then for all my turn, send the request and set status to notack
        val status = PROCESSORS.mapBy(j =>
            if (turn((i, j)) == "my") "notack" else "notsent"
        )
        {
            ...state,
            // store the type of communicate and the status
            communicate: state.communicate.set(
                i, { ...IDLE, request: m, status: status }
            ),
            // for each link initated by i and is my turn, update message. links on his turn will be updated when old ACK is received
            m: LINKS.mapBy(link =>
                if (link._1 == i and turn(link) == "my") m
                else state.m.get(link)
            ),
        }
    }

    action startW = all {
        canStartW(WRITER),
        // update val_i and start procedure communicate
        val v = state.val_i.get(WRITER) + 1
        val updated = beginCommunicate(WRITER, { kind: "W", label: v })
        state' = updated.with("val_i", state.val_i.set(WRITER, v)),
    }

    action startR1(i: int): bool = all{
        canStartR1(i),
        // start procedure communicate
        val updated = beginCommunicate(i, R1)
        state' = updated
    }

    // can send request if j is not crashed and the message in the link is a request
    def canReceiveRequest(link: Link): bool = not(state.crashed.contains(link._2)) and isRequest(state.m.get(link))

    // when receiving request, update j and send ACK
    action receiveRequest(link: Link): bool = all{
        canReceiveRequest(link),
        val val_j = state.val_i.get(link._2)
        val m = state.m.get(link)
        // ACK to be sent
        val ack = {
            kind: ackKind(m),
            label: if (m.kind == "R1") val_j else NO_INFO
        }
        // update state
        state' = {
            ...state,
            // for W and R2, m.label positive, choose max of val_i and val_j. For R1 m.label negative, always choose val_j
            val_i: state.val_i.set(link._2, maxLabel(val_j, m.label)),
            // update message at the link with ACK
            m: state.m.set(link, ack)
        }
    }

    // i can receive ACK if i is not crashed and there is an ACK in the link and in two situations
    def canReceiveACK(link: Link): bool = {
        val communicate = state.communicate.get(link._1)
        // i not crashed
        not(state.crashed.contains(link._1)) and 
        // an ACK in the link
        state.m.get(link) != EMPTY and 
        not(isRequest(state.m.get(link))) and
        // situation 1: i is IDLE, will consume this old ACK to free the link
        (communicate.request == EMPTY or 
        // situation 2: an active communicate for i
        // notsent: old ACK, will consume it, set the status to notack, and send the current request
        // notack: will record the ACK, set the status to ack, and increment numAck
        (communicate.numAck < QUORUM and Set("notsent", "notack").contains(communicate.status.get(link._2))))
    }

    // receive ACK, update info, and clear the link
    action receiveACK(link:Link): bool = all{
        canReceiveACK(link),
        val communicate = state.communicate.get(link._1)
        // old ACK of a finished communicate, clear the link
        state' =  if (communicate.request == EMPTY){
            state.with("m", state.m.set(link, EMPTY))
        // old ACK when a new communicate has started, clear the link, and send request of current communicate
        } else if (communicate.status.get(link._2) == "notsent"){
            val update = communicate.with("status", communicate.status.set(link._2, "notack"))
            {...state, communicate: state.communicate.set(link._1, update), m: state.m.set(link, communicate.request)}
        // ACK of current communicate, update status and info, increment numAck, and clear the lnk
        } else {
            val update = {
                ...communicate,
                status: communicate.status.set(link._2, "ack"),
                info: communicate.info.set(link._2, state.m.get(link).label),
                numAck: communicate.numAck + 1
            }
            {...state, communicate: state.communicate.set(link._1, update), m: state.m.set(link, EMPTY)}
        }
    }

    // i can finish its communicate procedure if it is not crashd and has received at least a majority of ACKs
    def canFinish(i: int): bool = not(state.crashed.contains(i)) and state.communicate.get(i).numAck >= QUORUM

    // finish communicate at processor i
    action finishCommunicate(i: int): bool = all{
        canFinish(i),
        val communicate = state.communicate.get(i)
        // finish R1, start R2 with the read value
        state' = if (communicate.request.kind == "R1"){
            val chosen = PROCESSORS.fold(0, (best, j) => max(best, communicate.info.get(j)))
            val update = beginCommunicate(i, {kind: "R2", label: chosen})
            // val_i could be updated during R1
            val newVal = max(chosen, state.val_i.get(i))
            update.with("val_i", state.val_i.set(i, newVal))
        } else {
            // finish W and R2, reset communicate
            {...state, communicate: state.communicate.set(i, IDLE)}
        }
    }

    // Crash-stop failures. Previously sent messages remain in their slots.
    def canCrash(i: int): bool =
        not(state.crashed.contains(i)) and state.crashed.size() < MAX_CRASHES

    // crash
    action crash(i: int): bool = all {
        canCrash(i),
        state' = state.with("crashed", state.crashed.union(Set(i))),
    }

    action disabled = all { false, state' = state }

    action step = any{
        // send Write request
        startW,
        { // send R1 request
            val ready = PROCESSORS.filter(i => canStart(i))
            if (ready.size() > 0) {
                nondet i = ready.oneOf()
                startR1(i)
            } else disabled
        },
        {
            // receive request on processor j or receive ACK on i
            val ready = LINKS.filter(link => canReceiveRequest(link) or canReceiveACK(link))
            if (ready.size() > 0) {
                nondet link = ready.oneOf()
                if (isRequest(state.m.get(link))) receiveRequest(link)
                else receiveACK(link)
            } else disabled
        },
        {
            // finish a communicate procedure on processor i
            val ready = PROCESSORS.filter(i => canFinish(i))
            if (ready.size() > 0) {
                nondet i = ready.oneOf()
                finishCommunicate(i)
            } else disabled
        },
        {
            // crash a processor
            val ready = PROCESSORS.filter(i => canCrash(i))
            if (ready.size() > 0) {
                nondet i = ready.oneOf()
                crash(i)
            } else disabled
        }
    }
}