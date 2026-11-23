# Indicator decomposition of the next state from four distinct lineages

Let `h` be a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of `n` genes, let `a`, `b`, `c`, `d` be genes and `t < n - 1`. Write `F(u)` for
the indicator that the four genes are in [four distinct lineages](apart4.md) after `u` events,
`A_xy(u)` for the [indicator](apart-ind.md) that `{x, y}` is [apart](pair-apart.md) after `u` events, and
`J_xy = F(t) (1 - A_xy(t + 1))`. Then

`F(t) A_ab(t + 1) A_cd(t + 1) = F(t + 1) + J_ac + J_ad + J_bc + J_bd`.

For a history in which the four genes are in four distinct lineages after `t` events
(`F(t) = 1`), `J_xy` is the indicator that `x` and `y` share a lineage after `t + 1` events, so
the identity says that `A_ab(t + 1) A_cd(t + 1)` is the number of the following events that
happen at step `t`: the four genes stay in four distinct lineages; `{a, c}` merges; `{a, d}`
merges; `{b, c}` merges; `{b, d}` merges. As the left side is `0` or `1`, at most one of these
events happens, and none happens when `{a, b}` or `{c, d}` merges. For a history with
`F(t) = 0`, both sides are `0`.
