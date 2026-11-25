# Unbiasedness and exact variance

**Unbiasedness and exact variance** (Irwin and Cheeseman 1939, p. 574; derived): let `d > 0`,
`n ≥ 1`, and let the true response probabilities satisfy `0 ≤ Pᵢ ≤ 1`, `P₀ = 0`, `P_k = 1`, and
be nondecreasing in dose (`Pᵢ ≤ Pᵢ₊₁` for `i < k`), so that the interpolated tolerance
distribution, with mass `Pᵢ₊₁ - Pᵢ ≥ 0` at `(xᵢ + xᵢ₊₁) / 2`, is a probability distribution.
For independent binomial(`n`, `Pᵢ`) counts at the doses `xᵢ = x₀ + i d`, the Spearman–Kärber
estimator `m` has expectation equal to the mean of the interpolated tolerance distribution,
`E[m] = ∑ᵢ (Pᵢ₊₁ - Pᵢ) (xᵢ + xᵢ₊₁) / 2`, and variance `E[(m - E[m])²] = d² ∑ᵢ Pᵢ (1 - Pᵢ) / n`.

## Sources

- Irwin and Cheeseman (1939), p. 574.
