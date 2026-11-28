# Finite subtheories of the theory of the real field are undecidable

Ziegler's theorem: every finite set of axioms in the language of rings that is true in the field of real numbers has an undecidable set of consequences. Hence no finitely axiomatized theory of fields that the reals satisfy is decidable, although the complete theory of real closed fields is.

**Theorem (Ziegler, 1982, as stated by Beklemishev, Dmitrieva and Makowsky).** Let $T$ be a finite set of first-order sentences in the language $\{+, \times\}$ of fields (with $0$, $1$, $-$ as usual) such that $(\mathbb{R}; +, \times) \models T$. Then the theory $\{\varphi : T \models \varphi\}$ is undecidable. The same holds for $T$ extended by the axioms saying that the characteristic is $0$, and for finite subtheories of the theory of the ordered field $(\mathbb{R}; +, \times, \leq)$, with or without the characteristic-$0$ axioms.

The extension to characteristic-$0$ axioms and to the ordered field is not stated by Ziegler but follows from his proof, as Beklemishev, Dmitrieva and Makowsky note. Since the theory of real closed fields is decidable by Tarski's quantifier elimination but is not finitely axiomatizable, the theorem shows that this decidability is not inherited by any finite part of it. In particular the theories of fields, of ordered fields, of Pythagorean fields and of Euclidean fields are undecidable.

## Depends on

- [Field](../../../Algebra/rings-and-fields/field.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Ziegler's proof (Theorem 1 and Corollary 1 of his paper) runs as follows. For every prime $q$ he constructs a subfield $K_q \subset \mathbb{R}$ in which the ring $(\mathbb Z, +, \times)$ is definable and every intermediate field $K_q \subseteq H \subset \mathbb{R}$ finite over $K_q$ has degree $1$ or a multiple of $q$. A non-principal ultraproduct $K$ of the fields $K_q$ is relatively algebraically closed in the corresponding ultrapower of $\mathbb{R}$, hence elementarily equivalent to $\mathbb{R}$, so $K \models T$; since $T$ is finite, some $K_q \models T$. Thus $T$ has a model in which $(\mathbb Z, +, \times)$ is interpretable, and the theorem of Tarski, Mostowski and Robinson, through the essential undecidability of the finitely axiomatized [Robinson arithmetic](../../first-order-logic/peano-arithmetic-and-robinson-s-q/qtheory.md), makes $T$ undecidable. The characteristic-$0$ and ordered versions follow because the same fields satisfy those axioms. A complete expansion links pages for the construction of the fields $K_q$, for the elementary equivalence of relatively algebraically closed subfields of real closed fields with $\mathbb{R}$, and for the theorem of Tarski, Mostowski and Robinson on finitely axiomatized theories with a model interpreting an essentially undecidable finitely axiomatized theory.

[Tarski's quantifier elimination over the reals](../quantifier-elimination-for-real-closed-fields/qe.md) makes the complete theory of $(\mathbb{R}; +, \times)$ decidable, so the theorem locates the source of undecidability in incompleteness: a finite theory true in $\mathbb{R}$ has many other models, and deciding consequence over all of them is impossible.

## Sources

- L. Beklemishev, A. Dmitrieva and J. A. Makowsky, "Axiomatizing origami planes", in *Dick de Jongh on Intuitionistic and Provability Logics* (eds. N. Bezhanishvili, R. Iemhoff and F. Yang), Outstanding Contributions to Logic, Springer, 2024, pp. 353–377, doi:10.1007/978-3-031-47921-2_12; read as arXiv:2012.03250v2, <https://arxiv.org/abs/2012.03250v2>: Theorem 2 in Section 6 (Ziegler's theorem with the characteristic-$0$ clause) and Theorem 5 in Section 8 (the ordered version), with the remark before Theorem 5 that the proof constructs a model of $T$ interpreting the ring of integers.
- M. Ziegler, "Einige unentscheidbare Körpertheorien", in *Logic and Algorithmic*, an international symposium held in honour of Ernst Specker, Monographies de L'Enseignement Mathématique, Geneva, 1982, pp. 381–392; read in the English translation by M. Beeson, "Some undecidable field theories", <https://www.michaelbeeson.com/research/papers/Ziegler.pdf>, cited by the source above: Theorem 1 and Corollary 1 with its proof.
