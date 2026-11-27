# At most five points on a circle form a Ramsey configuration

Let $1\le s\le5$ and let $a_i$, $i=0,\ldots,s-1$, be distinct points of $\mathbb R^2$, at a common real distance from some center. For each $r\ge2$ some $D\ge1$ has the property that every $r$-coloring of $\mathbb R^D$ contains $s$ identically colored labelled points with the same pairwise Euclidean distances as the $a_i$.

## Depends on

- [Indexed Euclidean Ramsey configurations](is-euclidean-ramsey.md)
- Finite injective planar configurations, common-radius circles and Euclidean Ramsey copies at the original scale.

## Proof depends on

- [Spherical quadratic-row sufficiency](independent-quadratic-evaluations-imply-ramsey.md)

## Proof outline

Separate the one- and two-point boundary cases from the rank theorem for full planar span. Prove the precise quadratic evaluation lemma on a circle before deriving the Ramsey consequence. The comparator does not exclude radius zero for one point.

- Circle evaluation-rank estimate for at most five points and sufficiency of the Euclidean Ramsey criterion after affine reduction.

## Sources

- [Comparator statement: `OAI.EuclideanRamsey.CircleConsequence.at_most_five_circle_points_ramsey`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EuclideanRamseyCircle.lean#L20-L25)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/172.md)
