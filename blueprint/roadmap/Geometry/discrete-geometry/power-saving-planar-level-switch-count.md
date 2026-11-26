# Power-saving bound for planar level switches

There are $\epsilon>0$ and $C\in\mathbb R$ such that for all $n\ge1$ and all generic planar configurations of $n$ labelled points the number of switches at every integer level $0\le k\le n$ is at most $C n^{4/3-\epsilon}$. Generic means injective, no three collinear, distinct first coordinates, distinct slopes for distinct unordered pairs, and no point in the interiors of two distinct pair-segments lying on a third distinct closed pair-segment. For $0<k<n$ a switch is an unordered pair whose line has exactly $k-1$ points with smaller value of $y-sx$, where $s$ is its slope; at levels zero and $n$ the count is zero.

## Depends on

- Generic slope and intersection conditions and switch count at each level.

## Proof outline

Define the count intrinsically and prove the bound before any perturbative transfer to halving pairs. Keep the all-orders qualifier and both endpoint levels.

- Uniform level complexity estimate with the power saving independent of level.

## Sources

- [Comparator statement: `OAI.PlanarHalving.power_bounds`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/HalvingLines.lean#L45-L53)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/183.md)
