# Satisfiability of ∀∃ HyperQPTL is undecidable

Already for HyperQPTL formulas with one universal trace quantifier followed by one existential trace quantifier, no algorithm decides whether some set of traces satisfies the formula; the $\exists^*\forall^*$ fragment, by contrast, is decidable.

**Theorem (Coenen, Finkbeiner, Hahn and Hofmann).** The satisfiability problem for [HyperQPTL](hyperqptl.md) formulas in the $\forall\exists$ fragment is undecidable: there is no algorithm that decides, for a closed HyperQPTL formula whose trace quantifier prefix is $\forall\pi\,\exists\pi'$, whether some set of traces satisfies it.

The $\exists^*\forall^*$ fragment of HyperQPTL has decidable satisfiability (Theorem 4.2 of the source), so it is the largest decidable fragment determined by the trace quantifier prefix.

## Depends on

- [HyperQPTL](hyperqptl.md)

## Proof depends on

None.

## Expansion

HyperLTL is a syntactic fragment of HyperQPTL, and Finkbeiner and Hahn proved that satisfiability of HyperLTL is undecidable for formulas with a $\forall\exists$ trace quantifier prefix (by a reduction from the Post correspondence problem). Undecidability therefore carries over to HyperQPTL.

## Sources

- N. Coenen, B. Finkbeiner, C. Hahn and J. Hofmann, "The hierarchy of hyperlogics", in *34th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2019)*, IEEE, 2019, pp. 1–13, doi:10.1109/LICS.2019.8785713; read as arXiv:2005.05934v1, <https://arxiv.org/abs/2005.05934v1>: Theorem 4.3 of arXiv:2005.05934v1, whose proof recalls the undecidability of $\forall\exists$ HyperLTL satisfiability from Finkbeiner and Hahn.
