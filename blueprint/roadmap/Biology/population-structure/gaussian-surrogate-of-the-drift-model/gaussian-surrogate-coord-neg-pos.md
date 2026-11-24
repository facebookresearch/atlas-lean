# Surrogate frequencies of positive variance can be negative

For finitely many populations and edges, every root mean `m`, real lineage weights `w` and
nonnegative edge lengths `ℓ`, let `X` be a population whose frequency has positive variance under
the [Gaussian surrogate](gaussian-surrogate.md), `Σ X X = ∑ e, w X e ^ 2 * ℓ e > 0` (the diagonal
entry of the [drift covariance matrix](drift-cov.md)). Then the surrogate gives positive probability
to the event that the frequency `x X` of `X` is negative. This holds whatever `m`, even for `m ≥ 1`:
unlike genuine allele frequencies, surrogate frequencies are not confined to `[0, 1]`.
