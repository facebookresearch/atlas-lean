# The remaining coalescence time of a pair still apart has mean one

Let `a` and `b` be genes, `t ≤ n - 1`, and `Y` a real function on the [ranked labeled histories](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of `n` genes that
[depends only on the first `t` steps](depends-before.md). Then

`∑_h Y(h) M_h({a, b}, t) = ∑_h Y(h) 1[{a, b} apart after t]`,

where the sums run over all histories and `M_h` is the
[conditional mean of the remaining coalescence time](future-mean.md). Under [random joining](../ranked-labeled-histories-of-coalescent-trees/random-joining.md) every history
has the [same probability](../ranked-labeled-histories-of-coalescent-trees/random-joining-singleton.md), so in the [Kingman genealogy](kingman-genealogy-measure.md) this says: given the first `t` steps, the remaining
coalescence time of `{a, b}` after `t` events has mean `1` if the pair is still apart, and `0`
otherwise.
