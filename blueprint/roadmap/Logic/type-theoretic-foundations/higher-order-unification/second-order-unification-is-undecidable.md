# Second-order unification is undecidable

There is no algorithm that decides whether two simply typed λ-terms whose free variables have types of order at most two can be made β-convertible by a substitution.

**Theorem (Goldfarb).** [Second-order unification](higher-order-unification-and-its-order.md) is undecidable.

The theorem sharpens the undecidability of third-order unification (Huet; Lucchesi). First-order unification is decidable. For second-order unification with only unary function symbols as constants (monadic second-order unification), Farmer proved decidability.

## Depends on

- [Higher-order unification and its order](higher-order-unification-and-its-order.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The DPRM theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

Goldfarb reduces Hilbert's tenth problem, the solvability of Diophantine equations, to second-order unification. Instead of Church numerals, Goldfarb encodes a number $n$ by the term $\lambda a.\, S^n a$ (a Goldfarb numeral), and each equation of a system of elementary Diophantine equations ($x = 1$, $x + y = z$, $x \cdot y = z$) becomes a unification constraint on second-order variables. A characteristic equation forces every solution of a variable to encode a number, and multiplication is captured by auxiliary equations whose solutions record a sequence of partial products. Spies and Forster give a version of this reduction to second-order unification (their Theorem 5.23 and Corollary 5.25).

## Sources

- W. D. Goldfarb, "The undecidability of the second-order unification problem", *Theoretical Computer Science* 13(2):225–230, 1981, doi:[10.1016/0304-3975(81)90040-2](https://doi.org/10.1016/0304-3975(81)90040-2) (original source, cited beside the copy read).
- S. Spies and Y. Forster, "Undecidability of higher-order unification formalised in Coq", in *Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP 2020)*, ACM, 2020, pp. 143–157, doi:[10.1145/3372885.3373832](https://doi.org/10.1145/3372885.3373832), read in the authors' open-access copy at <https://www.ps.uni-saarland.de/Publications/documents/SpiesForster_2019_UndecidabilityHOU.pdf>: Section 1 (history of the result) and Section 5 (second-order unification, Theorem 5.23 and Corollary 5.25).
- D. M. Cerna and J. Parsert, "One is all you need: second-order unification without first-order variables", *Logical Methods in Computer Science* 22(2), paper 3, 2026, doi:[10.46298/lmcs-22(2:3)2026](https://doi.org/10.46298/lmcs-22(2:3)2026). Numbering of the version read, arXiv:2404.10616v10: Section 1 (Goldfarb's theorem and the decidable monadic case).
