# Semiring homomorphisms commute with positive relational algebra

Let $K$ and $K'$ be commutative semirings and $h : K \to K'$ a semiring homomorphism, applied to
[$K$-relations](k-relations-and-positive-relational-algebra-over-a-semiring.md) pointwise: $h(R)(t) = h(R(t))$. Since
$h(0) = 0$, this keeps supports finite, so $h(R)$ is a $K'$-relation. Then $q(h(R)) = h(q(R))$ for every positive relational
algebra query $q$ and every $K$-relation $R$. The source states the converse as well, that a map commuting with all
these queries is a semiring homomorphism; as printed it fails, since the map sending every element to $0$ commutes with
every such query, all its images being empty, but does not send $1$ to $1$ when $0 \ne 1$ in $K'$.

## Depends on

- [K-relations and positive relational algebra over a semiring](k-relations-and-positive-relational-algebra-over-a-semiring.md)

## Sources

- T. J. Green, G. Karvounarakis and V. Tannen, *Provenance semirings*, PODS 2007, <http://www.cs.ucdavis.edu/~green/papers/pods07.pdf>, Proposition 3.5.
