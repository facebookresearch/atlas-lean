# Esteban–Torán: tree-like size is exponential in clause space

For every unsatisfiable CNF formula $\varphi$, the minimum number of nodes of a tree-like resolution refutation is at least $2^{\mathrm{Sp}(\varphi \vdash \bot) - 1} - 1$, where $\mathrm{Sp}$ is the clause space. More precisely, a tree-like refutation of Horton–Strahler number $d$ can be pebbled with $d + 1$ pebbles in the Esteban–Torán measure (so in clause space at most $d + 2$), and it has at least $2^{d+1} - 1$ nodes. Consequently clause space is at most $\log_2(\text{tree-like size} + 1) + 1$; in the Esteban–Torán measure the bound reads: tree-like size at least $2^{\mathrm{Sp}_{ET}} - 1$.

## Proof sketch

Pebble the tree in the order that evaluates first the child with the larger Horton–Strahler number, keeping one pebble on its root while the other child is pebbled; induction on the tree shows $d + 1$ pebbles suffice when a pebble may shift from a premise to the resolvent, and one extra clause covers the configuration measure. The node count bound comes from the embedded complete binary tree of height $d$.

## Depends on

- [Clause space of resolution refutations](clause-space-of-resolution.md)
- [Horton–Strahler number of a tree-like derivation](../tree-like-resolution/horton-strahler-number.md)

## Sources

- J. L. Esteban and J. Torán, "Space Bounds for Resolution", Information and Computation 171(1), 84–97, 2001: Theorem 7.
- J. Torán, "Space and Width in Propositional Resolution", Bulletin of the EATCS 83, 86–104, 2004: Theorem 9.
