# The theory of ordered origami planes is undecidable

Every extension of the theory of ordered metric Wu planes by finitely many axioms true in the ordered real plane is undecidable; in particular the theories of Euclidean ordered metric Wu planes and of ordered origami planes are undecidable.

**Theorem (Beklemishev, Dmitrieva and Makowsky).** Let $T$ be a finite set of sentences in the vocabulary $\tau_{o\text{-}wu}$ of incidence, orthogonality and betweenness such that the ordered real plane $\Pi_\mathbb{R} \models T$. Then the extension $T \cup \mathrm{OWU}$ of the theory $\mathrm{OWU}$ of [ordered metric Wu planes](metric-wu-planes-and-ordered-origami-planes.md) by $T$ is undecidable (Theorem 6 of the source).

**Corollary.** The first-order theories of Euclidean ordered metric Wu planes and of ordered origami planes are undecidable (Corollaries 3 and 4).

The corollary takes $T$ to be (H*5), respectively (H*5) and (H*6), which hold in $\Pi_\mathbb{R}$.

## Depends on

- [Metric Wu planes and ordered origami planes](metric-wu-planes-and-ordered-origami-planes.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Finite subtheories of the theory of the real field are undecidable](finite-subtheories-of-the-real-field-are.md)
- [Finite extensions of metric Wu plane geometry true in the real plane are undecidable](finite-extensions-of-metric-wu-plane-geometry.md)

## Expansion

Ordered metric Wu planes are bi-interpretable with ordered Pythagorean fields (Theorem 4 of the source), so the ordered version of Ziegler's theorem, for finite subtheories of the theory of the ordered real field, transfers as in the unordered case: a finite $\tau_{o\text{-}wu}$-theory $T$ true in $\Pi_\mathbb{R}$ translates into a finite theory of ordered fields true in $\mathbb{R}$, and consequence over $T \cup \mathrm{OWU}$ reduces computably to consequence over that theory together with the axioms of ordered Pythagorean fields. The corollary needs no further correspondence between the origami axioms and classes of fields: (H*5) and (H*6) are finitely many sentences true in $\Pi_\mathbb{R}$, so the theorem applies to them directly.

## Sources

- L. Beklemishev, A. Dmitrieva and J. A. Makowsky, "Axiomatizing origami planes", in *Dick de Jongh on Intuitionistic and Provability Logics* (eds. N. Bezhanishvili, R. Iemhoff and F. Yang), Outstanding Contributions to Logic, Springer, 2024, pp. 353–377, doi:10.1007/978-3-031-47921-2_12; read as arXiv:2012.03250v2, <https://arxiv.org/abs/2012.03250v2>: Theorem 6 (the ordered geometric version of Ziegler's theorem), Theorem 4 (ordered metric Wu planes and ordered Pythagorean fields) and Theorem 5 (the ordered version of Ziegler's theorem) in Section 8, and Corollaries 3 and 4 in Section 9 (the theories of Euclidean ordered Wu planes and of ordered Wu origami planes are undecidable).
