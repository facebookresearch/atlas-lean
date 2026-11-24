# Probability that an apart pair stays apart at the next step

Let `t < n - 1`, let `a` and `b` be genes and `Y` a real function on the [ranked labeled histories](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of `n` genes that
[depends only on the first `t` steps](depends-before.md). Then

`∑_h Y(h) A_h(t + 1) = (1 - 1/C(n - t, 2)) ∑_h Y(h) A_h(t)`,

where the sums run over all histories and `A_h(u)` is the [indicator](apart-ind.md) that
`{a, b}` is [apart](pair-apart.md) after `u` events of `h`. Under [random joining](../ranked-labeled-histories-of-coalescent-trees/random-joining.md) every history has the [same probability](../ranked-labeled-histories-of-coalescent-trees/random-joining-singleton.md), so this
says: given the first `t` steps, a pair still apart after `t` events remains apart after `t + 1`
events with probability `1 - 1/C(n - t, 2)`.
