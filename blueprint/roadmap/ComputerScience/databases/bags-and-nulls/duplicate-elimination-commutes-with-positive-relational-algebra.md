# Duplicate elimination commutes with positive relational algebra

Let $\delta : \mathbb{N} \to \mathbb{B}$ send $n$ to $[n \ge 1]$, and apply it to a bag relation tuple by tuple (duplicate elimination). Then
$\delta$ is a homomorphism of commutative semirings, and for every query $q$ of the positive relational algebra (selection, projection,
natural join, union, renaming) and every bag database $R$, $\delta(q(R)) = q_{\mathrm{set}}(\delta(R))$, where $q_{\mathrm{set}}$ is the same query
evaluated under set semantics.

## Proof

$\delta(0) = 0$, $\delta(1) = 1$, $\delta(m + n) = \delta(m) \vee \delta(n)$ and $\delta(mn) = \delta(m) \wedge \delta(n)$ for natural numbers, so $\delta$ is a
semiring homomorphism from $(\mathbb{N}, +, \cdot, 0, 1)$ to $(\mathbb{B}, \vee, \wedge, \bot, \top)$. Bag relations are the $\mathbb{N}$-relations and set
relations the $\mathbb{B}$-relations of the semiring-annotated model, and a semiring homomorphism applied tuple by tuple commutes with every
positive relational algebra query; this is proved by induction on the query, one operator at a time, for any number of input relations.

## Depends on

- [Bag relations and bag relational algebra](bag-relations-and-bag-relational-algebra.md)
- [K-relations and positive relational algebra over a semiring](../provenance-and-incremental-maintenance/k-relations-and-positive-relational-algebra-over-a-semiring.md)

## Proof depends on

- [Universality of provenance polynomials](../provenance-and-incremental-maintenance/universality-of-provenance-polynomials.md)

## Sources

- T. J. Green, G. Karvounarakis and V. Tannen, *Provenance semirings*, PODS 2007, Proposition 3.5 (the transformation given by $h : K \to K'$ commutes with every RA$^+$ query if and only if $h$ is a semiring homomorphism; stated there for queries of one argument). <http://www.cs.ucdavis.edu/~green/papers/pods07.pdf>
