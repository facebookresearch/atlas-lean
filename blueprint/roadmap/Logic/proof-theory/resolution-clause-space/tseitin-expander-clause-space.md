# Tseitin formulas on expanders need linear clause space

Let $G$ be a connected multigraph of maximum degree $k$ and $\chi$ a charge of odd total. Every resolution refutation of $T(G,\chi)$ in clause space $s$ satisfies $e(G) \le s + k - 3$. In particular, on constant-degree expanders with edge expansion $h(G) > 0$, clause space is at least $h(G)|V|/3 - k + 3$, which is linear in the number of variables.

## Proof sketch

Combine the width lower bound $e(G)$ for Tseitin formulas with the inequality $W \le s + k - 3$.

## Depends on

- [Tseitin formulas of a multigraph](../tseitin-formulas/tseitin-formulas-of-a-multigraph.md)
- [Clause space of resolution refutations](clause-space-of-resolution.md)
- [Ben-Sasson–Wigderson expansion of a multigraph](../tseitin-formulas/balanced-cut-expansion.md)

## Proof depends on

- [Resolution width of Tseitin formulas is at least the expansion](../tseitin-formulas/resolution-width-of-tseitin-formulas.md)
- [Atserias–Dalmau inequality: clause space bounds width](clause-space-bounds-width.md)

## Sources

- M. Alekhnovich, E. Ben-Sasson, A. A. Razborov and A. Wigderson, "Space Complexity in Propositional Calculus", SIAM Journal on Computing 31(4), 1184–1211, 2002.
- J. L. Esteban and J. Torán, "Space Bounds for Resolution", Information and Computation 171(1), 84–97, 2001: Theorem 19.
- E. Ben-Sasson and A. Wigderson, "Short Proofs Are Narrow — Resolution Made Simple", Journal of the ACM 48(2), 149–169, 2001.
- A. Atserias and V. Dalmau, "A Combinatorial Characterization of Resolution Width", Journal of Computer and System Sciences 74(3), 323–334, 2008.
