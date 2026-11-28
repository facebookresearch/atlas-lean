# Satisfiability of ∀∃ HyperCTL* is undecidable

Satisfiability of HyperCTL* is undecidable already for formulas with one universal followed by one existential path quantifier, while the $\exists^*\forall^*$ fragment is decidable.

**Theorem (Coenen, Finkbeiner, Hahn and Hofmann).** The satisfiability problem for [HyperCTL*](../hyperctl-star.md) formulas in the $\forall\exists$ fragment is undecidable: there is no algorithm that decides, for a HyperCTL* formula whose path quantifier prefix is $\forall\pi\,\exists\pi'$, whether some tree satisfies it, where trees are rooted $AP$-labelled trees (Section 2.1 of the source) and $\exists\pi$ at position $i$ ranges over the paths of the tree that agree up to position $i$ with the most recently quantified path, the root path at the start (Definition 3.5 of the source).

This sharpens the undecidability of general HyperCTL* satisfiability. The $\exists^*\forall^*$ fragment of HyperCTL* has decidable satisfiability (Theorem 4.7 of the source).

## Depends on

- [HyperCTL*](../hyperctl-star.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Satisfiability of ∀∃ HyperLTL is undecidable](satisfiability-of-forall-exists-hyperltl.md)

## Expansion

HyperCTL* subsumes HyperLTL as a syntactic fragment, and satisfiability of HyperLTL is undecidable for formulas with a $\forall\exists$ trace quantifier prefix (Finkbeiner and Hahn), which the source says gives the result (proof of Theorem 4.8). A HyperLTL model is a set of traces while a HyperCTL* model is a tree, and not every set of traces is the path set of a tree, so the transfer needs one more step; a good expansion adds a page showing that the $\forall\exists$ HyperLTL satisfiability problem remains undecidable over the path sets of trees (for instance by checking that the models built in Finkbeiner and Hahn's reduction can be taken to be such path sets).

## Sources

- N. Coenen, B. Finkbeiner, C. Hahn and J. Hofmann, "The hierarchy of hyperlogics", in *34th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2019)*, IEEE, 2019, pp. 1–13, doi:10.1109/LICS.2019.8785713; read as arXiv:2005.05934v1, <https://arxiv.org/abs/2005.05934v1>: Theorem 4.8 of arXiv:2005.05934v1, whose proof recalls the undecidability of $\forall\exists$ HyperLTL satisfiability from Finkbeiner and Hahn.
