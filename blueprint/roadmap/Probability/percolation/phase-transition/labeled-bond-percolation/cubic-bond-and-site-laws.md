# Cubic bond and site percolation and their origin thresholds

A bond of $\mathbb Z^3$ is represented by a vertex and one of the three positive coordinate directions; endpoint order is only an indexing convention. Bond configurations open these bonds by independent Bernoulli trials. Bond clusters use reachability along open bonds, including length-zero paths. Site configurations use independent Bernoulli trials on vertices; connect nearest neighbors only when both are open and assign the empty cluster to a closed site. Each model uses its own infimum over $p\in[0,1]$ with positive probability of an infinite origin cluster. A real Bernoulli parameter used outside that interval is clamped to it.

## Sources

- [Pinned source definition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CriticalZ3.lean#L9-L54)
