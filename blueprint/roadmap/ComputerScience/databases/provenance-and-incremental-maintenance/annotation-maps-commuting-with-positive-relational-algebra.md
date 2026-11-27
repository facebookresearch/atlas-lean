# A map of annotations commutes with positive relational algebra exactly when it preserves zero, sums and products

Let $K$ and $K'$ be commutative semirings and $h : K \to K'$ a map with $h(0) = 0$, applied to $K$-relations pointwise:
$h(R)(t) = h(R(t))$, which keeps supports finite, so $h(R)$ is a $K'$-relation. Then $q(h(R)) = h(q(R))$ for every positive
relational algebra query $q$ of one argument and every [$K$-relation](k-relations-and-positive-relational-algebra-over-a-semiring.md)
$R$, over relation schemas whose attribute domains have at least two values, if and only if $h(a + b) = h(a) + h(b)$ and
$h(a b) = h(a) h(b)$ for all $a, b \in K$: projecting two distinct tuples onto a common value adds their annotations, and
joining a relation with a renamed copy multiplies them. Without $h(0) = 0$ the pointwise image of the empty relation over an
infinite tuple universe has infinite support and is not a $K'$-relation. In particular every semiring homomorphism
commutes with these queries. The condition $h(1) = 1$ is not forced: the map sending every element to $0$ commutes with
every such query, since all its images are empty, but it is not a semiring homomorphism when $0 \ne 1$ in $K'$.

## Depends on

- [K-relations and positive relational algebra over a semiring](k-relations-and-positive-relational-algebra-over-a-semiring.md)

## Sources

- T. J. Green, G. Karvounarakis and V. Tannen, *Provenance semirings*, PODS 2007, <http://www.cs.ucdavis.edu/~green/papers/pods07.pdf>, Proposition 3.5.
