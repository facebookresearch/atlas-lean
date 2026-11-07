# Mean parametrization is the canonical `p`-parametrization

For `θ > 0` and `μ ≥ 0`,
`negBinomialReal θ μ` is `negBinomialPMF θ p` at `p = θ / (θ + μ)`, since
`1 - p = μ / (θ + μ)`. The two APIs are the same law; reuse the splitting and
conditioning results proved for `negBinomialPMF` through this equivalence.
