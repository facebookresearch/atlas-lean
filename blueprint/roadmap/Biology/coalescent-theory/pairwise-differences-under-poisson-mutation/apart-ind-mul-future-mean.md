# The mean remaining time of a pair vanishes once it has coalesced

For a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) `h`, genes `a` and `b` and a natural number `t`,

`1[{a, b} apart after t] · M_h({a, b}, t) = M_h({a, b}, t)`,

where `M_h` is the [conditional mean of the remaining coalescence time](future-mean.md). Hence
`M_h({a, b}, t) = 0` when `a` and `b` share a lineage after `t` events.
