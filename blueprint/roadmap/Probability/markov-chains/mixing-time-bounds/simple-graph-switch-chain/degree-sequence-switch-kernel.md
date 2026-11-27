# The lazy switch chain on labelled degree realizations

The states are simple graphs on a fixed finite labelled vertex set that realize the given degree at every vertex. A proposal is a four-element set with an ordered pair of distinct perfect matchings on it. If the first matching is present and the second is absent, remove the first and insert the second. Otherwise the proposal result is the original graph. Every permitted switch preserves each degree. The kernel entry from $G$ to $H$ is one half on the diagonal plus the number of proposals producing $H$ divided by $12\binom n4$. For $n\ge4$ this is a one-half hold and a one-half uniform proposal. At $n<4$ the ratio is totalized to zero, so the entry formula alone is not a probability kernel there. The reference law for the mixing claims is uniform over labelled degree realizations.

## Sources

- [Pinned source definition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SwitchChain.lean#L11-L94)
