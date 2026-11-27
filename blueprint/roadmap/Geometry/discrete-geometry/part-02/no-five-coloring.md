# No proper five-coloring of the unit-distance plane

There is no function $c:\mathbb C\to\{0,1,2,3,4\}$ such that $\|z-w\|=1$ implies $c(z)\ne c(w)$ for every $z,w\in\mathbb C$. The plane carries its ordinary Euclidean metric (complex modulus). The conclusion applies to arbitrary color classes, without measurability, continuity, or restrictions at boundaries.

## Depends on

- Unit-distance adjacency for the complex norm, and coloring by a total map into five labels.

## Proof depends on

- The source’s exclusion and compactness/transfer argument for arbitrary colorings, including the distinction from measurable colorings.

## Expansion

Keep the unrestricted domain in the entire proof: decompose the finite or limiting exclusions and prove that they imply nonexistence for arbitrary total colorings. The planar graph five-color theorem uses combinatorial planarity and does not settle this statement.

## Sources

- OpenAI Math, [`no_proper_five_coloring`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EuclideanFiveColor.lean#L10-L12) (statement and local definitions).
