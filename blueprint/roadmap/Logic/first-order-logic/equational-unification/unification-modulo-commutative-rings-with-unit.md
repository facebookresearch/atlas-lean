# Elementary unification modulo commutative rings with unit is undecidable

No algorithm decides whether an elementary unification problem modulo the theory of commutative rings with a multiplicative unit has a unifier.

**Theorem.** Let $\mathrm{CRU}$ be the equational theory of commutative rings with a multiplicative unit. Elementary $\mathrm{CRU}$-unification is undecidable: no algorithm decides whether a given elementary [E-unification problem](equational-unification-problems.md) modulo $\mathrm{CRU}$, built from the ring operations, $0$ and $1$ only, has a $\mathrm{CRU}$-unifier.

By contrast, unification modulo the theory of Boolean rings is decidable: NP-complete for elementary unification, $\Pi^p_2$-complete with constants and PSPACE-complete for general unification (Baader).

## Depends on

- [E-unification problems](equational-unification-problems.md)
- [Commutative ring with identity: a ring whose multiplication is commutative and has an identity element 1](../../../Algebra/rings-and-fields/commutative-ring-with-identity.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The source calls the undecidability an easy consequence of the undecidability of Hilbert's tenth problem (Matiyasevich; Davis), as sketched by Baader and Siekmann. Terms over the ring signature without free constants denote polynomials with integer coefficients, and an elementary problem $s =^?_{\mathrm{CRU}} t$ asks for a substitution of such terms for the variables that makes $s$ and $t$ equal modulo $\mathrm{CRU}$, which is a question about integer solutions of the polynomial equation $s = t$.

## Sources

- F. Baader and J. H. Siekmann, "Unification theory", in D. M. Gabbay, C. J. Hogger and J. A. Robinson (eds.), *Handbook of Logic in Artificial Intelligence and Logic Programming*, Vol. 2, Oxford University Press, 1994, pp. 41–125 (original sketch of the argument, cited beside the copy read).
- F. Baader and W. Snyder, "Unification theory", in A. Robinson and A. Voronkov (eds.), *Handbook of Automated Reasoning*, Vol. I, Elsevier, 2001, Chapter 8, pp. 445–533, doi:10.1016/B978-044450813-3/50010-2; read in the authors' open-access copy at <https://lat.inf.tu-dresden.de/research/papers/2001/BaaderSnyderHandbook.pdf>: Section 3.4, paragraph "Commutative and Boolean rings", which states the undecidability and the Boolean ring results.
