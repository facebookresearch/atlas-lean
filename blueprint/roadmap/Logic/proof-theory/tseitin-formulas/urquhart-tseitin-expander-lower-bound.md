# Urquhart: Tseitin formulas on expanders need exponential resolution refutations

There are constants $c, k > 0$ and a family of unsatisfiable $k$-CNF formulas $T_n$ (Tseitin formulas with odd total charge on constant-degree expander multigraphs with $\Theta(n)$ vertices) with $O(n)$ variables and $O(n)$ clauses such that every resolution refutation of $T_n$ has at least $2^{c n}$ lines.

## Proof sketch

Urquhart's original proof counts clauses through a bottleneck argument. Ben-Sasson and Wigderson reprove it: explicit constant-degree expanders have $h(G) \ge \varepsilon > 0$, so the width lower bound is linear, $e(G) \ge \varepsilon|V|/3$, while the number of edges is linear; the size–width tradeoff turns linear width into exponential size.

## Depends on

- [Tseitin formulas of a multigraph](tseitin-formulas-of-a-multigraph.md)
- [Constant-degree expanders exist on every finite vertex set](../../../GraphTheory/graph-families-and-operations/explicit-and-random-expander-constructions/constant-degree-expanders-exist.md)
- [Ben-Sasson–Wigderson expansion of a multigraph](balanced-cut-expansion.md)

## Proof depends on

- [Resolution width of Tseitin formulas is at least the expansion](resolution-width-of-tseitin-formulas.md)
- [Ben-Sasson–Wigderson for general resolution](../../propositional-logic/resolution-size-and-width/refutation-narrow.md)

## Sources

- A. Urquhart, "Hard Examples for Resolution", Journal of the ACM 34(1), 209–219, 1987.
- E. Ben-Sasson and A. Wigderson, "Short Proofs Are Narrow — Resolution Made Simple", Journal of the ACM 48(2), 149–169, 2001: Corollary 4.5.
