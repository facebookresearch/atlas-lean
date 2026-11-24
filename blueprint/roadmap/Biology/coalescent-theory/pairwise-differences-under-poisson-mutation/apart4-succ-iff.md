# Coordinates for the next step from four distinct lineages

Let `h` be a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of `n` genes and `t < n - 1`, and let the genes `a`, `b`, `c`, `d` be in
[four distinct lineages](apart4.md) after `t` events. Then there are points `z`, `s₁`, …, `s₆`
of `ℕ × ℕ`, with `s₁`, …, `s₆` pairwise distinct, such that after `t + 1` events the pairs
`{a, b}`, `{a, c}`, `{a, d}`, `{b, c}`, `{b, d}`, `{c, d}` are [apart](pair-apart.md) exactly when
`z ≠ s₁`, `z ≠ s₂`, `z ≠ s₃`, `z ≠ s₄`, `z ≠ s₅`, `z ≠ s₆` respectively. One can take for `z` the
sorted labels of the pair merged at step `t`, and for `s_i` the sorted labels of the lineages of
the `i`-th of these gene pairs after `t` events. In particular step `t` merges at most one of the
six pairs.
