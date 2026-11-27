# Brennan's area integrability for maps onto the disk

Let $W\subseteq\mathbb C$ be open, connected, and simply connected as a subspace, with at least two distinct points in the boundary of its image in the Riemann sphere. For every holomorphic bijection $\phi:W\to\mathbb D$ and every real $4/3<s<4$, the function $z\mapsto|\phi'(z)|^s$ is integrable on $W$ for planar Lebesgue area. Both endpoint inequalities are strict.

## Depends on

- [Open unit disk](../riemann-mapping-theorem/unit-disk.md).

Use the spherical frontier of the image of $W$, not just its frontier in the complex plane.

## Proof depends on

- [Derivative moments of univalent disk maps](univalent-disk-area-integrability.md), for the inverse map with exponent $2-s$.

## Proof strategy

Make the inverse derivative identity and the conformal area change-of-variables step explicit on the possibly unbounded domain $W$. Verify that $s\in(4/3,4)$ gives $2-s\in(-2,2/3)$ without adding boundary regularity.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Brennan.lean#L47-L49) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/072.md).
- OpenAI, [area integrability for maps onto the disk in the comparator proposition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Brennan.lean#L38-L42).
