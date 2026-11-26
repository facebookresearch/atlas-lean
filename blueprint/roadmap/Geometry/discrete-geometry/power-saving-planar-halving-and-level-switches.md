# Power-saving bound for planar halving pairs

There exist real $\epsilon>0,C$ and a natural cutoff $n_0$ such that for every even $n\ge n_0$ and every injective labelled $n$-point set in the plane with no three distinct points collinear, the number of unordered pairs whose line leaves $(n-2)/2$ other points on each open side is at most $C n^{4/3-\epsilon}$. Equivalently, count pairs $i<j$ with exactly that number of strictly positive and strictly negative orientation determinants against the remaining points. The companion [level-switch bound](power-saving-planar-level-switch-count.md) uses stronger genericity and different quantifiers.

## Depends on

- Orientation determinant, open half-plane counts, finite unordered labelled pairs.

## Proof depends on

- [Power saving for switch counts in generic position](power-saving-planar-level-switch-count.md)

## Expansion

Separate the perturbation bridge for a finite configuration of distinct points with no collinear triple: find a generic configuration with the same halving count, and identify that count with the middle switch count in even order. This bridge holds without a power-saving hypothesis and is independent of the linked uniform switch-count bound.

## Proof outline

Separate the bound in generic position and the step that extends it to configurations with only the noncollinearity condition. Preserve the eventual even-order restriction and the actual line-pair count.

## Sources

- [Comparator statement: `OAI.PlanarHalving.power_bounds`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/HalvingLines.lean#L45-L53)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/183.md)
- [Proof of the reduction and the prerequisite interfaces](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/HalvingLines/Main.lean)
