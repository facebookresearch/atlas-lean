# Positive relational algebra and nonrecursive Datalog agree on K-relations

Let $K$ be a commutative $\omega$-continuous semiring, $q$ a positive relational algebra query whose selection predicates only
test equality of attributes, and $q'$ the nonrecursive Datalog query obtained from $q$ by the standard translation. Then $q$,
evaluated on [$K$-relations](k-relations-and-positive-relational-algebra-over-a-semiring.md), and $q'$, evaluated with the
[Datalog semantics on $K$-relations](datalog-on-k-relations-over-omega-continuous-semirings.md), produce the same annotated
answer on every database of $K$-relations.

## Depends on

- [K-relations and positive relational algebra over a semiring](k-relations-and-positive-relational-algebra-over-a-semiring.md)
- [Datalog on K-relations over ω-continuous semirings](datalog-on-k-relations-over-omega-continuous-semirings.md)

## Sources

- T. J. Green, G. Karvounarakis and V. Tannen, *Provenance semirings*, PODS 2007, <http://www.cs.ucdavis.edu/~green/papers/pods07.pdf>, Proposition 5.3.
