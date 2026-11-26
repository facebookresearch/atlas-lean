# The stabbing planes proof system

Let $F$ be an unsatisfiable system of linear inequalities with integer coefficients, defining a polytope $P_F \subseteq [0,1]^n$ with no integer points (e.g. the standard translation of an unsatisfiable CNF). A **stabbing planes (SP) refutation** of $F$ is a binary tree whose nodes are labeled by polytopes, such that the root is $P_F$; each internal node $Q$ is labeled by a query $(a, b) \in \mathbb{Z}^n \times \mathbb{Z}$ and has the two children $Q \cap \{a \cdot x \ge b\}$ and $Q \cap \{a \cdot x \le b - 1\}$, discarding the integer-free slab $b - 1 < a \cdot x < b$; and every leaf polytope is empty, as certified by a nonnegative linear combination of its defining inequalities yielding $0 \ge 1$. The **size** is the number of nodes, the **depth** is the height of the tree, and the **coefficient size** is the maximum bit length of the queries.

## Depends on

- [Cook–Reckhow propositional proof systems](../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)
- [Tree-like resolution derivation](../../propositional-logic/resolution-size-and-width/resolution-tree.md)

## Sources

- P. Beame, N. Fleming, R. Impagliazzo, A. Kolokolova, D. Pankratov, T. Pitassi, R. Robere, "Stabbing planes", ITCS (2018), arXiv:1710.03219.
- N. Fleming, P. Kothari, T. Pitassi, "Semialgebraic proofs and efficient algorithm design", Foundations and Trends in Theoretical Computer Science 14 (2019).
