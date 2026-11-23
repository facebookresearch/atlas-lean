# Weighted sums over a state reached by $m$ choices of step $t$

Let `t < n - 1` and let `Y` be a real function on the [ranked labeled histories](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of `n` genes that [depends only on the first `t` steps](depends-before.md). Let `P` and
`E` be properties of histories such that `E` implies `P` and replacing step `t` of any history by
any [pair of lineages](../ranked-labeled-histories-of-coalescent-trees/lineage-pair.md) does not change whether `P` holds. Let `m` be a real number and suppose that,
for every history `f` with `P`, the number of the `C(n - t, 2)` pairs `x` for which the history
`f[t ↦ x]` (`f` with step `t` replaced by `x`) has `E` equals `m`. Then

`(∑_h Y(h) 1[E(h)]) · C(n - t, 2) = m ∑_h Y(h) 1[P(h)]`,

the sums running over all histories. Since `C(n - t, 2) > 0`, the sum of `Y` over the histories
with `E` is `m / C(n - t, 2)` times its sum over the histories with `P`. When no history has
`P`, nothing constrains `m` and both sides are `0`.
