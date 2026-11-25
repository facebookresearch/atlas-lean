# With λ > 0 a positive statistic has p-value below one

For real numbers `λ > 0` and `x > 0`, the [genomic-control p-value](gc-pvalue.md) is below `1`:

`P(χ²₁ > x / λ) < 1`.

The condition `λ > 0` is needed: for `λ < 0`, and for `λ = 0` with the convention `y / 0 = 0`,
the p-value of a positive statistic is `1`.
