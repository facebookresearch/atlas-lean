# Empirical Var

The **plug-in sample variance** `(1 / n) ∑_{i < n} (x i - x̄ₙ)²`, i.e. the variance of
the empirical distribution `empirical x n`. Its divisor is `n`, unlike the unbiased
`MathlibExt.Probability.Causality.sampleVar` (divisor `n - 1`); the bootstrap resamples from
the empirical distribution, so the plug-in variance is the one that appears.
