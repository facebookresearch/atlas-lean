# HyperCTL* satisfiability is undecidable

**Theorem (Clarkson, Finkbeiner, Koleini, Micinski, Rabe and Sánchez).** Finite-state satisfiability of [HyperCTL*](hyperctl-star.md) specifications, whether some finite Kripke structure
satisfies a given specification, is hard for [$\Sigma^0_1$](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md), and general satisfiability is hard for $\Sigma^1_1$. In particular both problems are undecidable.

The proof reduces LTL synthesis for distributed systems to satisfiability.

## Depends on

- [HyperCTL*](hyperctl-star.md)
- [The arithmetical class $\Sigma_n$](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)

## Expansion

This page becomes ready once:

- The undecidability of LTL synthesis for distributed architectures (Pnueli and Rosner), the source problem of the reduction (proof prerequisite; not yet stated)

## Sources

- M. R. Clarkson, B. Finkbeiner, M. Koleini, K. K. Micinski, M. N. Rabe and C. Sánchez, "Temporal logics for hyperproperties", *Principles of Security and Trust (POST 2014)*, Lecture Notes in Computer Science 8414, Springer, 2014, pp. 265–284, extended version arXiv:1401.4492, <https://arxiv.org/abs/1401.4492>: Section 6, Theorem 7, proved in Appendix C (Theorem 12).
