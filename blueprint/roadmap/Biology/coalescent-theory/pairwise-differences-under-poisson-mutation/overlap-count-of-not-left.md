# No lineage separates both pairs once the first pair has coalesced

Let `h` be a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md)
of a sample of `n` genes, let `u ≤ n - 1`, and let `a`, `b`, `c`, `d` be genes with `a ≠ b`
and `c ≠ d`. If `a` and `b` are in the same lineage after the first `u` events of `h`, then no
lineage after `u` events separates `{a, b}`, so the [overlap count](overlap-count.md) of
`{a, b}` and `{c, d}` after `u` events is `0`.
