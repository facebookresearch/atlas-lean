# Nagata’s strict inequality for very general plane points

For every integer $r\ge10$, there are countably many proper closed subsets of the space of ordered distinct $r$-tuples in $\mathbb P^2(\mathbb C)$, with nonempty common complement. Closed sets here are restrictions of common zero loci of multihomogeneous equations in the $r$ triples of projective coordinates. At every configuration $p$ in that complement and for every nonzero effective plane curve $C$ (including reducible and repeated components), every vector $m_i\in\mathbb N$ with $m_i\le\operatorname{mult}_{p_i}C$ satisfies $\sum_i m_i<\deg(C)\sqrt r$.

The curve is a nonzero finite cycle of homogeneous nonzero principal prime ideals. Its equation is a homogeneous polynomial realizing those factor weights; its degree is the total degree of that equation. Ordinary multiplicity is the least nonzero Taylor degree after dehomogenizing in a chart containing the marked point and translating it to the origin.

## Depends on

- [Equations of homogeneous plane cycles](homogeneous-plane-cycle-equation.md); chart independence of ordinary multiplicity and ideal-power membership.

## Proof depends on

- [Coordinate form of Nagata’s inequality](nagata-plane-polynomial.md) and comparison of multiplicity lower-bound predicates.

## Expansion

Transport arbitrary effective cycles through the equation construction, and show that the selected chart multiplicity implies the coordinate lower bound in every chart. Keep the strict inequality and the same exceptional family for all cycles and vectors.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Nagata.lean#L352-L364) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Nagata.lean).
