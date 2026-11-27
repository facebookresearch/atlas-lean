# Synchronization in broadcast networks is undecidable

The synchronization problem for broadcast protocols asks whether, for some number of processes, an execution brings every process into a given target state at the same time. No algorithm decides it. Restricted to Wait-Only protocols, it becomes decidable and Ackermann-complete.

**Problem (Guillou, Sangnier and Sznajder).** Synchro takes as input a [broadcast protocol](broadcast-protocols-and-their-networks.md) $\mathcal{P} = (Q, \Sigma, q_{in}, T)$ and a state $q_f \in Q$. The question is whether there exist an initial configuration $C$ (of some size $n \ge 1$, all processes in $q_{in}$) and a configuration $C'$ with $C \to^\ast C'$ and $C'(e) = q_f$ for every process $e \in \{1, \dots, \lVert C' \rVert\}$.

**Theorem (Guillou, Sangnier and Sznajder).** Synchro is undecidable.

The number of processes is existentially quantified: it is not part of the input. For Wait-Only protocols the same authors show that Synchro is decidable and Ackermann-complete, and that it is in EXPSPACE and EXPSPACE-hard when $q_f$ is a state with no outgoing reception.

## Depends on

- [Broadcast protocols and their networks](broadcast-protocols-and-their-networks.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces from the halting problem of deterministic two-counter machines with zero tests: given a machine with states $S$, initial state $s_{in}$ and final state $s_f$ without outgoing transitions, does $(s_{in}, 0, 0)$ reach $(s_f, 0, 0)$? The protocol lets one process (the leader) broadcast a start message $\ell$ and enter $s_{in}$; every other process goes to a state $0$. Afterwards the leader's state is the machine's state, and the number of processes in a state $x_1$ (resp. $x_2$) is the value of the first (resp. second) counter. A zero test is a broadcast by the leader of the message for $c_i = 0$; any process then sitting in $x_i$ receives it and falls into a sink state. An increment (decrement) is a broadcast by a process in $0$ (in $x_i$) that moves the leader and moves the broadcaster to $x_i$ (to $0$); any process that receives an operation message in the wrong place goes to the sink. When the leader reaches $s_f$ it broadcasts a final message $d$ that moves the processes in $0$ to $s_f$ and sends every process still in a counter state to the sink. So all processes can be gathered in $s_f$ exactly when the machine halts with both counters zero, using $1 + \max(x_1 + x_2)$ processes along the run.

A good expansion links the undecidability of the halting problem for two-counter machines (reaching the final state with both counters zero), which follows from the universality of two-counter machines and the undecidability of the halting problem for Turing machines but has no page of its own.

## Sources

- Lucie Guillou, Arnaud Sangnier and Nathalie Sznajder, "Wait-Only Broadcast Protocols Are Easier to Verify", 50th International Symposium on Mathematical Foundations of Computer Science (MFCS 2025), Leibniz International Proceedings in Informatics (LIPIcs) 345, pp. 53:1–53:17, 2025, <https://doi.org/10.4230/LIPIcs.MFCS.2025.53>. Read in arXiv:2506.22144v1, <https://arxiv.org/abs/2506.22144v1>; problem Synchro in Section 2.2, Theorem 2.4 (undecidability) with its proof in Appendix A, and the Wait-Only results in Sections 3 and 4, numbering of arXiv:2506.22144v1.
