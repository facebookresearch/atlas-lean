# Joint likelihood of the cell counts

For a finite set of cells `j` with real size factors `sⱼ`, counts `kⱼ ∈ ℕ` and a real `r`, the joint
likelihood is `L(k ∣ r) = ∏ⱼ e^(−sⱼ r) (sⱼ r)^(kⱼ) / kⱼ!`, the product of the
[Poisson likelihoods](poisson-exposure-lik.md). For `sⱼ ≥ 0` and `r ≥ 0` it is the probability of
the counts `k` when they are conditionally independent given `λ = r` with `kⱼ ~ Po(sⱼ r)`.
