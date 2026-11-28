# Hilbert's tenth problem is undecidable over large rings of S-integers in totally real fields and their quadratic extensions

Let $K$ be a totally real number field, a quadratic extension of one, or a number field over which some elliptic curve over $\mathbb{Q}$ gains no rank. For every $\varepsilon > 0$ there is a set $\mathcal{S}$ of primes of $K$ of natural density above $1 - 1/[K:\mathbb{Q}] - \varepsilon$ such that $\mathbb{Z}$ is Diophantine and Hilbert's tenth problem is undecidable over $\mathcal{O}_{K,\mathcal{S}}$.

For a number field $K$ and a set $\mathcal{S}$ of non-archimedean primes of $K$, let

$$
\mathcal{O}_{K,\mathcal{S}} = \{ x \in K : \operatorname{ord}_{\mathfrak{p}} x \ge 0 \text{ for every prime } \mathfrak{p} \notin \mathcal{S} \},
$$

so $\mathcal{O}_{K,\emptyset} = \mathcal{O}_K$ and $\mathcal{O}_{K,\mathcal{S}} = K$ when $\mathcal{S}$ contains every prime. The natural density of a set of primes of $K$ is taken among all primes of $K$, ordered by norm.

**Theorem (Shlapentokh).** Let $K$ be a number field satisfying one of the following:

- $K$ is totally real;
- $K$ is an extension of degree $2$ of a totally real number field;
- there is an elliptic curve $E$ defined over $\mathbb{Q}$ with $[E(K) : E(\mathbb{Q})] < \infty$.

Let $\varepsilon > 0$. Then there is a set $\mathcal{S}$ of non-archimedean primes of $K$ such that

1. the natural density of $\mathcal{S}$ is greater than $1 - \dfrac{1}{[K:\mathbb{Q}]} - \varepsilon$;
2. $\mathbb{Z}$ is Diophantine over $\mathcal{O}_{K,\mathcal{S}}$;
3. Hilbert's tenth problem over $\mathcal{O}_{K,\mathcal{S}}$ is undecidable.

Conventions: for $K = \mathbb{Q}$ the density bound is vacuous. The set $\mathcal{S}$ need not be computable, so Hilbert's tenth problem over $\mathcal{O}_{K,\mathcal{S}}$ is meant for rings of algebraic numbers, as on the linked definition page: coefficients are elements of $\mathcal{O}_{K,\mathcal{S}}$ given by their codes as algebraic numbers, with the promise that they lie in the ring.

## Depends on

- [Hilbert's tenth problem over a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/hilbert-s-tenth-problem-over-a-ring.md)
- [Integral closure of ℤ in a field and the ring of integers of a number field](../../algebraic-number-theory/number-fields-embeddings/ring-of-integers.md)
- [Diophantine subsets of a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/is-diophantine-set.md)
- [Field](../../../Algebra/rings-and-fields/field.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The primes allowed in denominators are, roughly, those without degree-one factors in a suitable extension, which is where the density $1 - 1/[K:\mathbb{Q}]$ comes from. Norm equations from such an extension, together with Pell-type equations in the totally real and quadratic cases or the finite-index elliptic curve in the third case, control the heights and the integrality of solutions at the remaining primes, and give a Diophantine definition of $\mathbb{Z}$ over $\mathcal{O}_{K,\mathcal{S}}$. Undecidability follows by Matiyasevich's theorem. The degree-two case is the main theorem of the source on extensions of degree $2$ of totally real fields, which extends the earlier totally real case. A good expansion links pages for the norm equations and the Pell-type or elliptic-curve arguments that bound heights, for the density computation of the allowed primes, and for the transfer of undecidability along a Diophantine definition of $\mathbb{Z}$.

## Sources

- Alexandra Shlapentokh, *Diophantine definability and decidability in extensions of degree 2 of totally real fields*, J. Algebra 313 (2007), no. 2, 846–896, https://doi.org/10.1016/j.jalgebra.2006.11.007; the first theorem stated at the end of the introduction of arXiv:math/0606368v1 gives the case of degree-2 extensions of totally real fields.
- Alexandra Shlapentokh, *Defining integers*, Bull. Symbolic Logic 17 (2011), no. 2, 230–251, https://doi.org/10.2178/bsl/1305810912; Theorem 7.2 of arXiv:1008.0809v1 states the result for all three types of fields, with references to the original papers.
