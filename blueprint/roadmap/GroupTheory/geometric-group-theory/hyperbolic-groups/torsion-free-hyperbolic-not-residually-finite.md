# A torsion-free word-hyperbolic group that is not residually finite

There is a group $G$ in which $g^m=1$ for $m>0$ implies $g=1$, with a finite generating set whose unit-edge Cayley graph is connected and has uniformly thin geodesic triangles, but $G$ is not residually finite. Thinness means that some integer $\delta\ge0$ works for every geodesic triangle: every vertex on each side lies within graph distance $\delta$ of one of the other two shortest-path sides. Failure of residual finiteness means a nonidentity element is killed by all homomorphisms to finite groups. Nonlinearity over every field is not a separate comparator conclusion.

## Depends on

- [Hyperbolic groups](is-hyperbolic.md), graph-metric thinness, ordinary torsion-freeness and separation by finite homomorphisms.

## Proof depends on

- The source group construction with simultaneously controlled torsion, hyperbolicity and a finite-quotient obstruction.

## Expansion

Compare the graph thinness definition including all three side conditions to the Atlas geometry API. Verify that the element killed in all finite quotients survives in the same group for which the hyperbolicity proof is given.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TorsionFreeHyperbolic.lean#L37-L40) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TorsionFreeHyperbolic.lean).
