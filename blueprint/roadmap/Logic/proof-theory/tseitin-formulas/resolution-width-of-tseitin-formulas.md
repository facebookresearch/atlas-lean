# Resolution width of Tseitin formulas is at least the expansion

Let $G$ be a connected multigraph with $|V| \ge 2$ and charge $\chi$ of odd total. Every resolution refutation of $T(G,\chi)$ contains a clause of width at least $e(G)$. Consequently, if every vertex has degree at most $k$, every refutation has at least $\exp\big(\Omega(\max(e(G) - k, 0)^2/|E|)\big)$ lines, and if $G$ has edge expansion $h(G) > 0$ the width is at least $h(G)|V|/3$.

## Proof sketch

Measure each clause $C$ by the least number of vertex constraints implying it. Axioms have measure $1$, the empty clause has measure $|V|$ (only all constraints together are contradictory), and measure is subadditive under resolution, so some clause has measure in $[|V|/3, 2|V|/3]$; for a minimal implying set $U$ every edge leaving $U$ must occur in $C$, giving width at least $e(G)$. The size bound follows from Ben-Sasson–Wigderson.

## Depends on

- [Tseitin formulas of a multigraph](tseitin-formulas-of-a-multigraph.md)
- [Ben-Sasson–Wigderson expansion of a multigraph](balanced-cut-expansion.md)
- [Width of a derivation](../../propositional-logic/resolution-size-and-width/derivation-width.md)

## Proof depends on

- [Tseitin formulas are unsatisfiable exactly when the total charge is odd](tseitin-formula-satisfiability.md)
- [Ben-Sasson–Wigderson for general resolution](../../propositional-logic/resolution-size-and-width/refutation-narrow.md)

## Sources

- E. Ben-Sasson and A. Wigderson, "Short Proofs Are Narrow — Resolution Made Simple", Journal of the ACM 48(2), 149–169, 2001: Theorem 4.4 (width), Corollary 3.6 (size from width) and Section 6.1 (proof).
- A. Urquhart, "Hard Examples for Resolution", Journal of the ACM 34(1), 209–219, 1987.
