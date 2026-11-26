# Padding an expansion of one without losing a prescribed denominator

For each natural $r\ge3$, let $n_0<\cdots<n_{r-1}$ be positive integer denominators whose reciprocals
sum to one. Given a natural $m$ occurring among them, there are $r+1$ strictly increasing positive
integer denominators whose reciprocals sum to one and among which $m$ occurs.

## Expansion

Split the largest unmarked denominator $b$, using $1/b=1/(b+1)+1/[b(b+1)]$ unless a new denominator equals the marker. In the collision cases, prove the prime obstruction by clearing denominators of smaller terms, then construct a collision-free composite split. Prove the replacement and sorting preserve the sum, the marker, and the increment in cardinality.

## Sources

- [EgyptianFractions.lean — `exact_marker_padding`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EgyptianFractions.lean#L78-L84)
