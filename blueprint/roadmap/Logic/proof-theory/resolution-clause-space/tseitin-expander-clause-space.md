# Tseitin formulas on expanders need linear clause space

Let $G = (V, E)$ be a connected graph of maximum degree $d$ that is an $(s, \delta)$-edge expander (every set $U$ of at most $s$ vertices has at least $\delta|U|$ edges with exactly one endpoint in $U$), and let $\chi$ be a charge under which $V$ has odd total charge. Then every resolution refutation of the Tseitin formula $T(G,\chi)$ has clause space at least $\delta s/d$. In particular, on graphs of constant degree that are $(\alpha|V|, \delta)$-edge expanders for constants $\alpha, \delta > 0$, clause space is linear in the number of variables.

## Proof sketch

Filmus et al. measure a configuration by the size of a smallest vertex set whose parity constraints imply it, show that some configuration of the refutation has measure between $s/d$ and $s$, and use expansion to show that such a configuration has at least $\delta$ times its measure many clauses. (Derived, not stated in this form by the sources: combining the width lower bound $e(G)$ for Tseitin formulas with the space–width inequality $W \le \mathrm{Sp} + k - 3$ for $k$-CNF formulas gives $e(G) \le \mathrm{Sp} + k - 3$ for every connected multigraph of maximum degree $k$, and on expanders with edge expansion $h(G) > 0$ clause space at least $h(G)|V|/3 - k + 3$.)

## Depends on

- [Tseitin formulas of a multigraph](../tseitin-formulas/tseitin-formulas-of-a-multigraph.md)
- [Clause space of resolution refutations](clause-space-of-resolution.md)

## Proof depends on

- [Ben-Sasson–Wigderson expansion of a multigraph](../tseitin-formulas/balanced-cut-expansion.md)
- [Resolution width of Tseitin formulas is at least the expansion](../tseitin-formulas/resolution-width-of-tseitin-formulas.md)
- [Atserias–Dalmau inequality: clause space bounds width](clause-space-bounds-width.md)

## Sources

- Y. Filmus, M. Lauria, M. Mikša, J. Nordström and M. Vinyals, "From Small Space to Small Width in Resolution", 31st Symposium on Theoretical Aspects of Computer Science (STACS 2014), LIPIcs 25, 2014: Definitions 7–8 and Theorem 9 (originally proved by Alekhnovich et al. and by Esteban and Torán), and Theorem 1 (the space–width inequality used in the derived remark).
- M. Alekhnovich, E. Ben-Sasson, A. A. Razborov and A. Wigderson, "Space Complexity in Propositional Calculus", SIAM Journal on Computing 31(4), 1184–1211, 2002.
- J. L. Esteban and J. Torán, "Space Bounds for Resolution", Information and Computation 171(1), 84–97, 2001: Theorem 19.
- E. Ben-Sasson and A. Wigderson, "Short Proofs Are Narrow — Resolution Made Simple", Journal of the ACM 48(2), 149–169, 2001.
- A. Atserias and V. Dalmau, "A Combinatorial Characterization of Resolution Width", Journal of Computer and System Sciences 74(3), 323–334, 2008.
