# Finite subtheories of the theory of the real field are undecidable

Ziegler's theorem: every finite set of axioms in the language of rings that is true in the field of real numbers has an undecidable set of consequences. Hence no finitely axiomatized theory of fields that the reals satisfy is decidable, although the complete theory of real closed fields is.

**Theorem (Ziegler, *L'Enseignement Mathématique* 28, 1982, as stated in the source).** Let $T$ be a finite set of first-order sentences in the language $\{+, \times\}$ of fields (with $0$, $1$, $-$ as usual) such that $(\mathbb{R}; +, \times) \models T$. Then the theory $\{\varphi : T \models \varphi\}$ is undecidable. The same holds for $T$ extended by the axioms saying that the characteristic is $0$, and for finite subtheories of the theory of the ordered field $(\mathbb{R}; +, \times, \leq)$, with or without the characteristic-$0$ axioms.

The extension to characteristic-$0$ axioms and to the ordered field is not stated by Ziegler but follows from his proof, as Beklemishev, Dmitrieva and Makowsky note. Since the theory of real closed fields is decidable by Tarski's quantifier elimination but is not finitely axiomatizable, the theorem shows that this decidability is not inherited by any finite part of it. In particular the theories of fields, of ordered fields, of Pythagorean fields and of Euclidean fields are undecidable.

## Depends on

- [Field](../../../Algebra/rings-and-fields/field.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Tarski's [quantifier elimination over the reals](../quantifier-elimination-for-real-closed-fields/qe.md) makes the complete theory of $(\mathbb{R}; +, \times)$ decidable, so the theorem locates the source of undecidability in incompleteness: a finite theory true in $\mathbb{R}$ has many other models, and deciding consequence over all of them is impossible. Combined with bi-interpretations between geometric and field theories, the theorem yields undecidability of axiomatic plane geometries, such as metric Wu planes and ordered origami planes, whose coordinate fields are Pythagorean, Euclidean or Vieta fields.

## Sources

- L. Beklemishev, A. Dmitrieva and J. A. Makowsky, "Axiomatizing origami planes", in *Larisa Maksimova on Implication, Interpolation, and Definability*, Outstanding Contributions to Logic 28, Springer, 2024, pp. 353–377, doi:10.1007/978-3-031-47921-2_12; read as arXiv:2012.03250v2, <https://arxiv.org/abs/2012.03250v2>: the statement of Ziegler's theorem in the section "Undecidability", with the characteristic-$0$ clause, and its ordered version in the section "Ordered metric Wu planes and Pythagorean fields".
