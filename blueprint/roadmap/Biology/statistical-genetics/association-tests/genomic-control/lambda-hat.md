# Mean-based estimate of the genomic-control factor

For real scores `z_0, …, z_{m-1}` of `m` genes, whose 1-df association statistics are `zₖ²`, the
mean-based genomic-control estimate of the inflation factor is the mean of the `m` statistics,

`λ̂ = (1 / m) ∑ₖ zₖ²`.

It is computed as `(∑ₖ zₖ²) / m` with the convention `x / 0 = 0`: for `m = 0` genes the sum is empty
and `λ̂ = 0`, which is not a mean of any statistics. The intended domain is `m ≥ 1`.
