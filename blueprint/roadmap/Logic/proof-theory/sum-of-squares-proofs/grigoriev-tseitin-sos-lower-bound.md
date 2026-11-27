# Grigoriev: sum-of-squares degree lower bound for Tseitin parity systems

Let $G_k$ be an $r$-regular expander on $k$ vertices ($r$ a constant) with a charge $\chi$ of odd total. Over a real field, every Positivstellensatz refutation of the Boolean binomial system of the Tseitin formula (the $\pm 1$ encoding $\prod_{e \ni v} y_e = (-1)^{\chi(v)}$, $y_e^2 = 1$) has degree $\Omega(k)$, linear in the number of variables. More generally, for any Boolean binomial system the Positivstellensatz degree is at least half of its refutation degree $D$, the least degree within which Laurent-monomial derivations reach a constant other than $1$. Since static sum-of-squares refutations are special Positivstellensatz refutations, the bound applies to them.

## Proof sketch

A product of vertex equations is the equation of the edge boundary of the set $U$ of multiplied vertices, with sign given by the charge of $U$. Deriving $-1 = 1$ needs all $k$ vertices, so some intermediate Laurent monomial involves between $k/3$ and $2k/3$ vertices, and expansion gives it degree $\Omega(k)$; thus $D = \Omega(k)$. Below degree $D/2$, the linear map sending each monomial equivalent to a constant $b$ to $b$, and every other monomial to $0$, is nonnegative on squares and vanishes on the ideal, which rules out a refutation. Schoenebeck's lemma gives the same kind of bound from width lower bounds.

## Depends on

- [Parity systems and bounded-width derivations](parity-systems-and-bounded-width-derivations.md)
- [Tseitin formulas of a multigraph](../tseitin-formulas/tseitin-formulas-of-a-multigraph.md)
- [Positivstellensatz (sum-of-squares) refutations](positivstellensatz-refutations.md)

## Proof depends on

- [Schoenebeck's lemma: width lower bounds give SOS pseudo-expectations for parity](schoenebeck-lemma.md)
- [Tseitin formulas are unsatisfiable exactly when the total charge is odd](../tseitin-formulas/tseitin-formula-satisfiability.md)

## Sources

- D. Grigoriev, "Linear Lower Bound on Degrees of Positivstellensatz Calculus Proofs for the Parity", Theoretical Computer Science 259(1–2), 613–622, 2001: Theorem (Section 2), Lemma 8 and Corollary 1 (Section 3).
- G. Schoenebeck, "Linear Level Lasserre Lower Bounds for Certain k-CSPs", Proceedings of the 49th IEEE Symposium on Foundations of Computer Science (FOCS), 2008.
