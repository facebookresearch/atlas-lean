# Hilbert's tenth problem is undecidable over both subrings of the rationals given by a complementary pair of prime sets

There is a partition of the prime numbers into two computable sets $\mathcal{S}$ and $\mathcal{T}$ such that Hilbert's tenth problem is undecidable over both rings $\mathcal{O}_{\mathbb{Q},\mathcal{S}}$ and $\mathcal{O}_{\mathbb{Q},\mathcal{T}}$ of rational numbers with denominators divisible only by primes in $\mathcal{S}$, respectively in $\mathcal{T}$.

For a set $\mathcal{S}$ of prime numbers let $\mathcal{O}_{\mathbb{Q},\mathcal{S}} = \{x \in \mathbb{Q} : \operatorname{ord}_p x \ge 0 \text{ for all primes } p \notin \mathcal{S}\}$. Two sets $\mathcal{S}, \mathcal{T}$ of primes are *exactly complementary* when $\mathcal{S} \cup \mathcal{T}$ is the set of all primes and $\mathcal{S} \cap \mathcal{T} = \emptyset$.

**Theorem (Eisenträger–Everest).** There are exactly complementary computable sets of primes $\mathcal{S}$ and $\mathcal{T}$ such that Hilbert's tenth problem is undecidable over $\mathcal{O}_{\mathbb{Q},\mathcal{S}}$ and over $\mathcal{O}_{\mathbb{Q},\mathcal{T}}$.

Conventions: computability of $\mathcal{S}$ and $\mathcal{T}$ makes both rings computable. Hilbert's tenth problem is undecidable over every subring $\mathcal{O}_{\mathbb{Q},\mathcal{S}}$ with $\mathcal{S}$ finite, by Julia Robinson's work (Theorem 3.6 and Corollary 3.7 of arXiv:1008.0809v1); the content of the theorem is that a single partition of the primes gives undecidability on both sides.

## Depends on

- [Hilbert's tenth problem over a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/hilbert-s-tenth-problem-over-a-ring.md)
- [Commutative ring with identity](../../../Algebra/rings-and-fields/commutative-ring-with-identity.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

Eisenträger and Everest extend Poonen's method (see [Poonen's theorem on large subrings of the rationals](h10-over-subrings-of-q-inverting-density-one.md)), which models the integers by approximation with multiples of a point of infinite order on a rank-one elliptic curve and which only constrains density-zero sets of primes to lie in, or outside, the set of inverted primes. Using descent on elliptic curves, they arrange such constraints for both rings at once, so that each of $\mathcal{O}_{\mathbb{Q},\mathcal{S}}$ and $\mathcal{O}_{\mathbb{Q},\mathcal{T}}$ carries a Diophantine model of $\mathbb{Z}$, and Matiyasevich's theorem gives undecidability on both sides. A good expansion links pages for Poonen's construction of a Diophantine model of $\mathbb{Z}$ over large subrings of $\mathbb{Q}$, for the descent on elliptic curves that Eisenträger and Everest use, and for the transfer of undecidability along a Diophantine model.

## Sources

- Kirsten Eisenträger and Graham Everest, *Descent on elliptic curves and Hilbert's tenth problem*, Proc. Amer. Math. Soc. 137 (2009), no. 6, 1951–1959, https://doi.org/10.1090/S0002-9939-08-09740-2; the statement as recalled in Theorem 4.2 of the version of the survey below that was read.
- Alexandra Shlapentokh, *Defining integers*, Bull. Symbolic Logic 17 (2011), no. 2, 230–251, https://doi.org/10.2178/bsl/1305810912; the statement is Theorem 4.2 of arXiv:1008.0809v1.
