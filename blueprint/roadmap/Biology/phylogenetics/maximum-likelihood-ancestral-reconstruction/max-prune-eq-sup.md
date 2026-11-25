# The max-product recursion computes the maximal labeling weight

If $\mathrm{obs}(l, s) \ge 0$ for all $l, s$ and the tree $t$ has [nonnegative weights](nonneg-weights.md), then for every state $s$,

$$M(t, s) = \max_{z} W(t, s, z),$$

the maximum over all [labelings](../felsenstein-s-pruning-algorithm/labeling.md) $z$ of their [weights](../felsenstein-s-pruning-algorithm/weight.md), where $M$ is the [max-product recursion](max-prune.md).
