# Grigoriev: sum-of-squares degree lower bound for Tseitin parity systems

Let $G$ be a connected multigraph with charge $\chi$ of odd total. The $\pm1$ encoding of the Tseitin parity system of $(G,\chi)$ has no sum-of-squares refutation of degree less than $e(G)$ (the minimum balanced cut). On constant-degree expanders with edge expansion $h(G) > 0$ every SOS refutation has degree at least $h(G)|V|/3$, linear in the number of variables; hence the Lasserre hierarchy needs linearly many levels to refute random-like parity systems.

## Proof sketch

A sum of vertex equations is the equation of the edge boundary of the set $U$ of summed vertices, with right-hand side the charge of $U$. Below width $e(G)$ every derivable equation comes from a set $U$ smaller than a third of the vertices, whose charge differs from the complement's, so $0 = 1$ is not derivable; apply Schoenebeck's lemma.

## Depends on

- [Parity systems and bounded-width derivations](parity-systems-and-bounded-width-derivations.md)
- [Tseitin formulas of a multigraph](../tseitin-formulas/tseitin-formulas-of-a-multigraph.md)
- [Ben-Sasson–Wigderson expansion of a multigraph](../tseitin-formulas/balanced-cut-expansion.md)

## Proof depends on

- [Schoenebeck's lemma: width lower bounds give SOS pseudo-expectations for parity](schoenebeck-lemma.md)
- [Tseitin formulas are unsatisfiable exactly when the total charge is odd](../tseitin-formulas/tseitin-formula-satisfiability.md)

## Sources

- D. Grigoriev, "Linear Lower Bound on Degrees of Positivstellensatz Calculus Proofs for the Parity", Theoretical Computer Science 259(1–2), 613–622, 2001.
- G. Schoenebeck, "Linear Level Lasserre Lower Bounds for Certain k-CSPs", Proceedings of the 49th IEEE Symposium on Foundations of Computer Science (FOCS), 2008.
