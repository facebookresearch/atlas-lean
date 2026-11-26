# Finite transitive configurations have Ramsey subsets

Let $a$ and $y$ be injective finite indexed configurations in the same $\mathbb R^D$, with $a$ nonempty and its range contained in the range of $y$. Assume the group of permutations of the indices of $y$ preserving all labelled distances acts transitively: for every $i,j$ there is such a permutation sending $i$ to $j$. Then for each integer $r\ge2$ there is a positive-dimensional Euclidean space in which every $r$-coloring contains a monochromatic distance-preserving copy of $a$.

## Depends on

- [Indexed Euclidean Ramsey configurations](is-euclidean-ramsey.md)
- Indexed Euclidean Ramsey property, finite transitivity via distance permutations, and inclusion of ranges.

## Proof depends on

- [Sufficiency of the tensor certificate](euclidean-ramsey-tensor-field-criterion.md)

## Proof outline

Separate the transitive parent from inheritance by its nonempty subsets. Match the finite-distance permutation group to the chosen proof substrate, and do not assume a matching affine span for the two sets.

- Orbit-sum invariance and averaging a tensor certificate after affine reduction, or an equivalent finite-group Ramsey argument with exact scale.

## Sources

- [Comparator statement: `OAI.EuclideanRamsey.TransitiveConsequence.subset_of_finite_transitive_ramsey`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EuclideanRamseyTransitive.lean#L19-L26)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/172.md)
