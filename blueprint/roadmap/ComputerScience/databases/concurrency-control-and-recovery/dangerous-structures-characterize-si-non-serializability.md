# Dangerous structures in non-serializable SI histories

Let $H$ be a multiversion history produced under snapshot isolation, and let $\mathrm{DSG}(H)$ be its dependency
serialization graph, whose edges are the wr-, ww- and rw-dependencies between its committed transactions; $H$ is
serializable whenever $\mathrm{DSG}(H)$ is acyclic. If $H$ is not serializable, then $\mathrm{DSG}(H)$ has a cycle,
and every cycle in it contains three consecutive transactions $T_1, T_2, T_3$ (with $T_1 = T_3$ possible) such that
$T_1$ and $T_2$ are concurrent with an rw-antidependency edge $T_1 \to T_2$, and $T_2$ and $T_3$ are concurrent with
an rw-antidependency edge $T_2 \to T_3$ (Fekete et al., Theorem 2.1). The converse fails: if $T_1$, $T_2$, $T_3$
start together, $T_1$ reads $x$, $T_2$ reads $y$ and writes $x$, $T_3$ writes $y$, and all three commit, then
$T_1 \to T_2 \to T_3$ is such a structure, yet $\mathrm{DSG}(H)$ has no cycle and $H$ is serializable in the order
$T_1, T_2, T_3$. The statement is a necessary condition for non-serializability, not a characterization.

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: the dependency serialization graph of a multiversion history (wr-, ww- and rw-dependency
  edges with respect to the version order) and concurrency of transactions.

## Depends on

- [Snapshot isolation and the write-skew anomaly](snapshot-isolation-and-the-write-skew-anomaly.md)
- [Multiversion histories and one-copy serializability](remaining-clauses-of-multiversion-histories-and-one-copy-ser.md)

## Sources

- A. Fekete, D. Liarokapis, E. O'Neil, P. O'Neil and D. Shasha, *Making snapshot isolation serializable*, ACM TODS 30(2), 2005, Definition 1.1 (p. 495) and Theorem 2.1 (p. 506); the theorem is also quoted on Dennis Shasha's page for the paper. <https://cs.nyu.edu/~shasha/papers/serializablesnap>
