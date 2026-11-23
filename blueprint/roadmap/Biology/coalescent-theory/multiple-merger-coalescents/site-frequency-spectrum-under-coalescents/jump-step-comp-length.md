# The jump chain seen through the number of blocks

Let `Λ` be a finite measure on `[0, 1]` and `b` a list of `|b|` block sizes with
`λ_{|b|} ≠ 0`. For every function `h` of the number of blocks, the
[transition operator](jump-step.md) gives
`∑_{k=2}^{|b|} (C(|b|, k) λ_{|b|,k} / λ_{|b|}) h(|b| + 1 - k)`: the number of blocks moves from
`|b|` to `|b| + 1 - k` with probability `C(|b|, k) λ_{|b|,k} / λ_{|b|}`, which is the jump chain
of the [block-counting process](../../coalescents/block-counting-generator.md).
