# Root-relative second moment in the drift model

In a [drift model](drift-model.md) on a measure `μ`, with root frequency `r` and
[population frequencies](freq.md) `p X`, the root-relative second moment of populations `X`, `Y` is
`Σ(X, Y) = ∫ (p X - r) * (p Y - r) dμ`, the integral of the product of their frequency changes from
the root (an expectation when `μ` is a probability measure). The integrand is integrable, since the
root and the population frequencies are square integrable.
