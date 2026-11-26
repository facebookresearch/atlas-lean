# Stabbing planes simulate cutting planes and equal tree-like R(CP)

Every cutting planes refutation of size $s$ of a system $F$ can be converted into a stabbing planes refutation of $F$ of size $O(s)$ and depth $O(s)$. Moreover stabbing planes is polynomially equivalent to the tree-like version of Krajíček's system $\mathrm{R(CP)}$, whose lines are disjunctions of linear inequalities, and it simulates tree-like resolution, DPLL with branching on linear inequalities, and branch-and-cut integer programming.

## Proof sketch

For each Chvátal-Gomory cut $a \cdot x \ge \lceil b \rceil$ derived from $a \cdot x \ge b$, query $(a, \lceil b\rceil)$: the branch $a \cdot x \le \lceil b \rceil - 1$ is immediately empty by the derivation's linear combination, so only the other branch continues; following the derivation in topological order yields a path-like tree. The equivalence with tree-like $\mathrm{R(CP)}$ maps each node to the disjunction of the negations of its branch conditions.

## Depends on

- [The stabbing planes proof system](stabbing-planes-system.md)
- [Krajíček's R(CP): resolution over linear inequalities](rcp-system.md)

## Sources

- P. Beame, N. Fleming, R. Impagliazzo, A. Kolokolova, D. Pankratov, T. Pitassi, R. Robere, "Stabbing planes", ITCS (2018), arXiv:1710.03219.
- J. Krajíček, "Discretely ordered modules as a first-order extension of the cutting planes proof system", Journal of Symbolic Logic 63 (1998) 1582-1596.
