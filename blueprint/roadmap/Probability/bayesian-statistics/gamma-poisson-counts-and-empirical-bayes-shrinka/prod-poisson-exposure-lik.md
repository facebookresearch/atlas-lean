# Factorization of the joint likelihood

For a finite set of cells `i` with real size factors `sᵢ`, counts `kᵢ ∈ ℕ` and a real `r`,
`∏ᵢ e^(−sᵢ r) (sᵢ r)^(kᵢ) / kᵢ! = (∏ᵢ sᵢ^(kᵢ) / kᵢ!) · r^K e^(−S r)` with `K = ∑ᵢ kᵢ` and
`S = ∑ᵢ sᵢ`: the product of the [Poisson likelihoods](poisson-exposure-lik.md) depends on the rate
through `(K, S)` only.
