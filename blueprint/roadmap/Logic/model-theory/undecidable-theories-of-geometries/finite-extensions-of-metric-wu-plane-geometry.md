# Finite extensions of metric Wu plane geometry true in the real plane are undecidable

A geometric form of Ziegler's theorem: adding to the axioms of metric Wu planes any finite set of axioms true in the real plane leaves an undecidable theory. In particular the theory of metric Wu planes is undecidable.

**Theorem (Beklemishev, Dmitrieva and Makowsky).** Let $T$ be a finite set of sentences in the vocabulary $\tau_{wu}$ of incidence and orthogonality such that the real plane $\Pi_\mathbb{R} \models T$. Then the theory $T \cup \mathrm{WU}$, where $\mathrm{WU}$ is the first-order theory of [metric Wu planes](metric-wu-planes-and-ordered-origami-planes.md), is undecidable (Theorem 3 of the source).

**Corollary.** The first-order theory of metric Wu planes is undecidable ($T = \varnothing$; Corollary 2).

## Depends on

- [Metric Wu planes and ordered origami planes](metric-wu-planes-and-ordered-origami-planes.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Finite subtheories of the theory of the real field are undecidable](finite-subtheories-of-the-real-field-are.md)

## Expansion

Metric Wu planes and Pythagorean fields of characteristic $0$ are bi-interpretable: every such field $F$ gives the coordinate plane $PP^*_{wu}(F)$, a metric Wu plane, and every metric Wu plane $\Pi$ gives a coordinate field $RF^*_{field}(\Pi)$ defined from two intersecting lines and a unit point, with definable isomorphisms $RF^*_{field}(PP^*_{wu}(F)) \cong F$ and $PP^*_{wu}(RF^*_{field}(\Pi)) \cong \Pi$. Translating $T$ into the language of fields gives a finite set $T'$ true in $\mathbb{R}$, and the bi-interpretation shows that $T' \cup \mathrm{PF} \models \varphi$ iff $T \cup \mathrm{WU} \models \forall \ell_0, m_0, Z_0\,(\mathit{Par}(\ell_0, m_0, Z_0) \to \varphi^{wu})$, where $\mathrm{PF}$ is the theory of Pythagorean fields of characteristic $0$ and $\mathit{Par}$ says the parameters form a coordinate frame. By Ziegler's theorem $T' \cup \mathrm{PF}$ is undecidable, and the translation is computable. A good expansion links a page for the bi-interpretation of metric Wu planes with Pythagorean fields of characteristic $0$ (Theorem 1 of the source) and the equivalence (3) it yields.

## Sources

- L. Beklemishev, A. Dmitrieva and J. A. Makowsky, "Axiomatizing origami planes", in *Dick de Jongh on Intuitionistic and Provability Logics* (eds. N. Bezhanishvili, R. Iemhoff and F. Yang), Outstanding Contributions to Logic, Springer, 2024, pp. 353–377, doi:10.1007/978-3-031-47921-2_12; read as arXiv:2012.03250v2, <https://arxiv.org/abs/2012.03250v2>: Theorem 3 (the geometric version of Ziegler's theorem) and Corollary 2 in Section 6, "Undecidability", with Theorem 1, the bi-interpretation theorem of Section 5.
