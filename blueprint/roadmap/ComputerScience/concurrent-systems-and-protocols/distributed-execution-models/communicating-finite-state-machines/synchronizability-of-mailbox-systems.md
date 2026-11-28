# Synchronizability of mailbox systems with accepting states is undecidable

For networks of finite automata that communicate asynchronously through one FIFO mailbox per participant, it is undecidable whether the sequences of sends of accepted executions are the same as under synchronous communication, once the automata may have accepting states.

**Setting (Di Giusto, Laversa and Peters).** A *network of communicating automata* $\mathcal N = ((A_p)_{p \in P}, M)$ has a finite set $P$ of participants and a finite set $M$ of messages, each with a sender and a receiver; each $A_p = (S_p, s_{0,p}, M, \delta_p, F_p)$ is a finite automaton with initial state $s_{0,p}$, final states $F_p$ and transitions labeled by sends $p!q\,a$ and receives $p?q\,a$ of $p$. In the *mailbox* semantics each participant $q$ has one FIFO buffer $b_q$: a send of $a$ to $q$ appends $a$ to $b_q$, whatever the sender, and $q$ receives $a$ only when $a$ is at the head of $b_q$. In the *synchronous* semantics a send and the matching receive happen in one step. An *execution* is a sequence of actions from the initial configuration (initial states, empty buffers) to a *final* configuration, in which every participant is in a final state; its *trace* is its projection on send actions. The mailbox system is *synchronizable* if its set of traces equals that of the synchronous system. The *generalized synchronizability problem* asks this for networks with arbitrary final states; the *synchronizability problem* restricts to networks in which all states are final.

**Theorem (Di Giusto, Laversa and Peters).** The generalized synchronizability problem for mailbox systems is undecidable.

The accepting states are essential to the proof. For the synchronizability problem itself (all states final) and mailbox communication the question was left open, and the same paper shows it decidable when the communication topology is a tree. For peer-to-peer channels, with all states accepting, synchronizability is undecidable by a result of Finkel and Lozes ([synchronizability of communicating finite-state machines is undecidable](synchronizability-is-undecidable.md)).

## Depends on

- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

From an instance $(w_1, \dots, w_n), (w'_1, \dots, w'_n)$ of Post's correspondence problem the reduction builds four automata: $A_I$ guesses a sequence of indices and sends it, followed by an end marker, to both $A_W$ and $A_{W'}$, which send the letters of the corresponding words $w_i$, respectively $w'_i$, to $A_L$. The checker $A_L$ reads the letters from its mailbox alternately from the two senders and compares them; if everything matches, including the end markers, it sends a message $\mathit{ok}$ that nobody receives and moves to its only accepting state. Additional receptions make all other behavior synchronizable, and the final configuration reached after $\mathit{ok}$ can only be reached asynchronously. Hence the network is not synchronizable if and only if the instance has a solution.

## Sources

- Cinzia Di Giusto, Laetitia Laversa and Kirstin Peters, "Synchronisability in Mailbox Communication", in *Proceedings of the Combined 31st International Workshop on Expressiveness in Concurrency and 21st Workshop on Structural Operational Semantics (EXPRESS/SOS 2024)*, Electronic Proceedings in Theoretical Computer Science 412, 2024, pp. 19–34, doi:[10.4204/EPTCS.412.3](https://doi.org/10.4204/EPTCS.412.3); read in arXiv:2411.14580v1 ([arXiv](https://arxiv.org/abs/2411.14580v1)), cited by section: Section 2 (networks, mailbox and synchronous systems, executions, traces, synchronizability and the two problems), Section 3 (the encoding of Post's correspondence problem and the undecidability theorem) and Section 4 (tree topologies).
