# Satisfiability of ∀∃ HyperCTL* is undecidable

Satisfiability of HyperCTL* is undecidable already for formulas with one universal followed by one existential path quantifier, while the $\exists^*\forall^*$ fragment is decidable.

**Theorem (Coenen, Finkbeiner, Hahn and Hofmann).** The satisfiability problem for [HyperCTL*](../hyperctl-star.md) formulas in the $\forall\exists$ fragment is undecidable: there is no algorithm that decides, for a HyperCTL* formula whose path quantifier prefix is $\forall\pi\,\exists\pi'$, whether some tree satisfies it.

This sharpens the undecidability of general HyperCTL* satisfiability. The $\exists^*\forall^*$ fragment of HyperCTL* has decidable satisfiability (Theorem 4.7 of the source).

## Depends on

- [HyperCTL*](../hyperctl-star.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

HyperCTL* subsumes HyperLTL as a syntactic fragment, and satisfiability of HyperLTL is undecidable for formulas with a $\forall\exists$ trace quantifier prefix (Finkbeiner and Hahn), which gives the result.

## Sources

- N. Coenen, B. Finkbeiner, C. Hahn and J. Hofmann, "The hierarchy of hyperlogics", in *34th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2019)*, IEEE, 2019, pp. 1–13, doi:10.1109/LICS.2019.8785713; read as arXiv:2005.05934v1, <https://arxiv.org/abs/2005.05934v1>: Theorem 4.8 of arXiv:2005.05934v1, whose proof recalls the undecidability of $\forall\exists$ HyperLTL satisfiability from Finkbeiner and Hahn.
