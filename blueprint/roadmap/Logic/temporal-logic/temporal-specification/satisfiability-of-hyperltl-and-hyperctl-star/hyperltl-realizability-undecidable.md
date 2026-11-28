# Realizability of ∀∃ HyperLTL is undecidable

No algorithm decides whether a HyperLTL formula over inputs and outputs is realized by some strategy, already for formulas whose quantifier prefix is one universal followed by one existential trace quantifier; synthesis is also undecidable for the purely universal fragment.

**Setting.** For atomic propositions $\mathrm{AP} = I \cup O$ split into inputs and outputs, a *strategy* $f\colon (2^I)^* \to 2^O$ produces one trace for every infinite input sequence, and a [HyperLTL](../hyperltl.md) formula $\varphi$ is *realizable* if some strategy's set of traces satisfies $\varphi$, as for [HyperQPTL realizability](../hyperqptl/realizability-of-hyperqptl-formulas.md). The *synthesis* problem asks to decide realizability (and construct a strategy). $\forall^*$ is the fragment whose trace quantifier prefix is purely universal, and $\forall^*\exists^*$ the fragment whose prefix is a block of universal quantifiers followed by a block of existential ones.

**Theorem (Finkbeiner, Hahn, Lukert, Stenger and Tentrup).** Realizability of $\forall^*\exists^*$ HyperLTL is undecidable, already for formulas with one universal and one existential trace quantifier ($\forall^1\exists^1$) (Theorem 5 of the source).

The source also shows that the synthesis problem for universal HyperLTL, the $\forall^*$ fragment, is undecidable (Theorem 2).

Both results are in Section 3 of the source. By contrast, realizability is PSPACE-complete for the $\exists^*$ fragment (Corollary 1), decidable for $\exists^*\forall^1$ (Theorem 4) and for the linear $\forall^*$ fragment (Theorem 3), undecidable for $\exists^*\forall^{>1}$, and the $\forall^1$ case is LTL realizability.

## Depends on

- [HyperLTL](../hyperltl.md)
- [Realizability of HyperQPTL formulas](../hyperqptl/realizability-of-hyperqptl-formulas.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

For the universal fragment, universal trace quantifiers express that one output may depend only on certain inputs, which encodes a distributed architecture with two processes receiving different inputs; LTL synthesis for that architecture is undecidable (Finkbeiner and Schewe, LICS 2005, as cited by the source). For $\forall^1\exists^1$, a reduction from the Post correspondence problem lets the existential trace check the next step of a candidate solution, following Finkbeiner and Hahn's undecidability proof for HyperLTL satisfiability. A complete expansion of the universal case links the undecidability of LTL synthesis for distributed architectures with information forks, which has no page here.

## Sources

- Bernd Finkbeiner, Christopher Hahn, Philip Lukert, Marvin Stenger and Leander Tentrup, "Synthesizing reactive systems from hyperproperties", in *Computer Aided Verification (CAV 2018)*, Lecture Notes in Computer Science 10981, 289–306, Springer, 2018, doi:[10.1007/978-3-319-96145-3_16](https://doi.org/10.1007/978-3-319-96145-3_16). Numbering of the version read, arXiv:1905.13511v1: Definition 1, Table 1, Corollary 1 and Theorems 2–5 in Section 3, and the appendix proof of Theorem 5.
