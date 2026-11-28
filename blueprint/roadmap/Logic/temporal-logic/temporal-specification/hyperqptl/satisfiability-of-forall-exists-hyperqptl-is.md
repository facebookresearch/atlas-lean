# Satisfiability of ∀∃ HyperQPTL is undecidable

Already for HyperQPTL formulas with one universal trace quantifier followed by one existential trace quantifier, no algorithm decides whether some nonempty set of traces satisfies the formula; the $\exists^*\forall^*$ fragment, by contrast, is decidable.

**Theorem (Coenen, Finkbeiner, Hahn and Hofmann).** The satisfiability problem for [HyperQPTL](hyperqptl.md) formulas in the $\forall\exists$ fragment is undecidable: there is no algorithm that decides, for a closed HyperQPTL formula whose trace quantifier prefix is $\forall\pi\,\exists\pi'$, whether some nonempty set of traces satisfies it. The set must be nonempty: the empty set satisfies every formula whose first trace quantifier is universal, so the source's question, whether a trace set $T$ with $T \models \varphi$ exists, is read for nonempty $T$, as in Finkbeiner and Hahn's HyperLTL-SAT, from which the source inherits the result.

The $\exists^*\forall^*$ fragment of HyperQPTL has decidable satisfiability (Theorem 4.2 of the source), so it is the largest decidable fragment determined by the trace quantifier prefix.

## Depends on

- [HyperQPTL](hyperqptl.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Satisfiability of ∀∃ HyperLTL is undecidable](../satisfiability-of-hyperltl-and-hyperctl-star/satisfiability-of-forall-exists-hyperltl.md)

## Expansion

HyperLTL is a syntactic fragment of HyperQPTL, and Finkbeiner and Hahn proved that satisfiability of HyperLTL is undecidable for formulas with a $\forall\exists$ trace quantifier prefix (by a reduction from the Post correspondence problem). Undecidability therefore carries over to HyperQPTL.

## Sources

- N. Coenen, B. Finkbeiner, C. Hahn and J. Hofmann, "The hierarchy of hyperlogics", in *34th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2019)*, IEEE, 2019, pp. 1–13, doi:10.1109/LICS.2019.8785713; read as arXiv:2005.05934v1, <https://arxiv.org/abs/2005.05934v1>: Theorem 4.3 of arXiv:2005.05934v1, whose proof recalls the undecidability of $\forall\exists$ HyperLTL satisfiability from Finkbeiner and Hahn.
