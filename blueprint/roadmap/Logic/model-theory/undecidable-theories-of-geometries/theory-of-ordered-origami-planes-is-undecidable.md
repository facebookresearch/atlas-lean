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

## Expansion

Ordered metric Wu planes are bi-interpretable with ordered Pythagorean fields (Theorem 4 of the source), and the ordered version of Ziegler's theorem (Theorem 5 of the source, for finite subtheories of the theory of the ordered field $(\mathbb{R}; +, \times, \le)$) transfers by the technique of Theorem 3. Let $T$ be a finite $\tau_{o\text{-}wu}$-theory true in $\Pi_\mathbb{R}$, let $T' = \{\theta^{\mathrm{field}} : \theta \in T\}$ be its translation into the language of ordered fields, and let $\mathrm{OPF}$ be the axioms of ordered Pythagorean fields. The ordered analogue of equation (3) of the source holds: $T' \cup \mathrm{OPF} \models \varphi$ iff $T \cup \mathrm{OWU} \models \forall \ell_0, m_0, Z_0\,(\mathrm{Par}(\ell_0, m_0, Z_0) \to \varphi^{o\text{-}wu})$. Since $T' \cup \mathrm{OPF}$ is a finite set of sentences true in $(\mathbb{R}; +, \times, \le)$, it is undecidable by Theorem 5, and the computable map $\varphi \mapsto \forall \ell_0, m_0, Z_0\,(\mathrm{Par}(\ell_0, m_0, Z_0) \to \varphi^{o\text{-}wu})$ reduces it to $T \cup \mathrm{OWU}$, which is therefore undecidable. A good expansion links a page for the bi-interpretation of ordered metric Wu planes with ordered Pythagorean fields (Theorem 4) and the ordered analogue of (3) it yields. The corollary needs no further correspondence between the origami axioms and classes of fields: (H*5) and (H*6) are finitely many sentences true in $\Pi_\mathbb{R}$, so the theorem applies to them directly.

## Sources

- L. Beklemishev, A. Dmitrieva and J. A. Makowsky, "Axiomatizing origami planes", in *Dick de Jongh on Intuitionistic and Provability Logics* (eds. N. Bezhanishvili, R. Iemhoff and F. Yang), Outstanding Contributions to Logic, Springer, 2024, pp. 353–377, doi:10.1007/978-3-031-47921-2_12; read as arXiv:2012.03250v2, <https://arxiv.org/abs/2012.03250v2>: Theorem 6 (the ordered geometric version of Ziegler's theorem), equation (3) with its proof in Section 6 (the technique of Theorem 3), Theorem 4 (ordered metric Wu planes and ordered Pythagorean fields) and Theorem 5 (the ordered version of Ziegler's theorem) in Section 8, and Corollaries 3 and 4 in Section 9 (the theories of Euclidean ordered Wu planes and of ordered Wu origami planes are undecidable).
