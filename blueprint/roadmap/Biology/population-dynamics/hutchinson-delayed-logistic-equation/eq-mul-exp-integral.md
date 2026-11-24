# Integral representation of delayed logistic solutions

For real numbers `r`, `K` and `τ ≥ 0`, every [solution](is-solution.md) `x` of the delayed logistic
equation `x'(t) = r x(t) (1 - x(t - τ) / K)` with history `φ` satisfies
`x(t) = x(0) exp(r ∫₀ᵗ (1 - x(s - τ) / K) ds)` for every `t ≥ 0`, where `x(0) = φ(0)`. With the
convention `a / 0 = 0`, for `K = 0` this reads `x(t) = x(0) e^{r t}`.
