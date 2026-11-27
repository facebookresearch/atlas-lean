# HyperLTL model checking is PSPACE-hard in the system size

**Theorem.** There is a fixed [HyperLTL](hyperltl.md) formula $\psi$ such that deciding, for a given Kripke structure $K$, whether $K$ satisfies $\psi$ is hard for
[PSPACE](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/pspace.md): model checking is PSPACE-hard in the size of the system. The formula comes from the encoding of SecLTL
and has positive [alternation depth](hyperctl-star.md). For fixed formulas of alternation depth $0$ the problem is in [NLOGSPACE](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/nl.md) in the size of the structure, by
the complexity of HyperCTL* model checking with $k = 0$, so the hardness needs an alternation.

## Depends on

- [HyperLTL](hyperltl.md)
- [Polynomial space for decision problems](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/pspace.md)
- [HyperCTL*](hyperctl-star.md)
- [The complexity class NL](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/nl.md)

## Proof depends on

- [Complexity of HyperCTL* model checking](model-checking-hyperctl-star-by-alternation-depth.md)

## Expansion

This page becomes ready once:

- Model checking SecLTL is PSPACE-hard in the size of the Kripke structure (Dimitrova, Finkbeiner, Kovács, Rabe and Seidl), and the encoding of SecLTL into HyperCTL*, Theorem 4 of the source, which yields a HyperLTL formula here (proof prerequisites; not yet stated)

## Sources

- M. R. Clarkson, B. Finkbeiner, M. Koleini, K. K. Micinski, M. N. Rabe and C. Sánchez, "Temporal logics for hyperproperties", *Principles of Security and Trust (POST 2014)*, Lecture Notes in Computer Science 8414, Springer, 2014, pp. 265–284, extended version arXiv:1401.4492, <https://arxiv.org/abs/1401.4492>: Section 5.3 (Theorem 4 and the PSPACE-hardness for a fixed specification of alternation depth at least $1$, via SecLTL), Section 6, Theorem 5 (with $g_c(-1, y) = \log y$) and the lower bounds in $|K|$ before Theorem 6, and Theorem 6.
