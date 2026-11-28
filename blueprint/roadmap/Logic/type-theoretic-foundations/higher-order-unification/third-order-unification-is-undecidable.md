# Third-order unification is undecidable

There is no algorithm that decides whether two simply typed λ-terms whose free variables have types of order at most three can be made β-convertible by a substitution.

**Theorem (Huet; Lucchesi).** [Third-order unification](higher-order-unification-and-its-order.md) is undecidable. Consequently higher-order unification in the simply typed λ-calculus is undecidable.

Huet and Lucchesi proved this independently, and Goldfarb later lowered the order to two. First-order unification is decidable.

## Depends on

- [Higher-order unification and its order](higher-order-unification-and-its-order.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

Both original proofs reduce Post's correspondence problem. Spies and Forster give a simplified version of Huet's proof as a reduction from the modified correspondence problem, in which a solution must start with a fixed first pair (their Theorem 4.7). The reduction produces third-order unification problems that are solvable exactly when the correspondence instance has a solution.

## Sources

- G. P. Huet, "The undecidability of unification in third order logic", *Information and Control* 22(3):257–267, 1973, doi:[10.1016/S0019-9958(73)90301-X](https://doi.org/10.1016/S0019-9958(73)90301-X) (original source, cited beside the copy read).
- S. Spies and Y. Forster, "Undecidability of higher-order unification formalised in Coq", in *Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP 2020)*, ACM, 2020, pp. 143–157, doi:[10.1145/3372885.3373832](https://doi.org/10.1145/3372885.3373832), read in the authors' open-access copy at <https://www.ps.uni-saarland.de/Publications/documents/SpiesForster_2019_UndecidabilityHOU.pdf>: Section 1 (history of the result) and Section 4 (third-order unification, Theorem 4.7).
