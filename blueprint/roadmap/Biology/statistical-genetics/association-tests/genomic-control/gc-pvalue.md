# Genomic-control p-value

For real numbers `λ` and `x`, the genomic-control p-value of a 1-df statistic `x` with inflation
factor `λ` is the [`χ²₁` tail](chi-sq-one-tail.md) at `x / λ`, as a real number:

`P(χ²₁ > x / λ)`.

It is meant for `λ > 0` and a statistic `x ≥ 0`. It is `1` whenever `x / λ ≤ 0`; in particular,
with the convention `y / 0 = 0`, it is `1` at `λ = 0`.
