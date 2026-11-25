# Consistent cuts and their lattice

Fix a finite set $E$ of events of a distributed computation of $n$ processes, partially ordered by the causality (happened-before) relation $<$, with an initial event for each process.

- **Cuts.** A *cut* of $E$ is a finite subset $C \subseteq E$ that contains the initial event of every process and, with any event of a process, all earlier events of the same process. A cut $C_2$ is *later than* $C_1$ if $C_1 \subseteq C_2$. With union and intersection the cuts form a lattice.
- **Consistent cuts.** A cut $C$ is *consistent* if it is left-closed under causality: $e' \in C$ and $e < e'$ imply $e \in C$. Equivalently, every message received in $C$ was sent in $C$. The consistent cuts are closed under union and intersection, so they form a sublattice of the lattice of cuts. Any finitely many consistent cuts therefore have a consistent cut later than all of them, namely their union, and one earlier than all of them, namely their intersection.
- **Vector-time criterion.** Let each event $e$ carry its vector timestamp $C(e) \in \mathbb{N}^n$. For a cut $X$ whose last events on the processes are $c_1, \dots, c_n$, put $t_X = \sup(C(c_1), \dots, C(c_n))$, the componentwise maximum. Then $X$ is consistent if and only if $t_X = (C(c_1)[1], \dots, C(c_n)[n])$, that is, $C(c_j)[i] \le C(c_i)[i]$ for all $i, j$.
- **Isomorphism.** The lattice of consistent cuts is isomorphic to the lattice of possible time vectors of $E$, ordered componentwise.

The global state of a consistent cut consists of the local state of each process at its cut event, together with the messages sent but not yet received.

## Sources

- F. Mattern, "Virtual time and global states of distributed systems", in *Parallel and Distributed Algorithms*, North-Holland, 1989, pp. 215–226, <https://www.vs.inf.ethz.ch/publ/papers/VirtTimeGlobStates.pdf>: Section 3 (cuts, Theorem 1; Definition 3, consistent cuts; Theorem 2, the sublattice of consistent cuts), Section 4 (global states of consistent cuts), Definition 5 and Theorem 6 (global time of a cut and the consistency criterion), and Theorems 8 and 9 (lattice of possible time vectors and the isomorphism).
