# Branch-length classes under growth are square integrable

Let `μ` be a probability measure, let `ρ ≥ 0` and let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) of a
sample of size `n` under `μ`, each `T_k` measurable: for `2 ≤ k ≤ n`, `T_k` has the exponential
law with rate `C(k, 2)`, and `T_2, …, T_n` are independent. Let `T^ρ_k` (`k ∈ ℕ`) be the
[time-changed holding times](growth-times.md) for exponential growth at rate `ρ`: the epoch with
`k` lineages lasts `T^ρ_k = G(V_k) - G(V_{k+1})` in real time, with `V_k = ∑_{j=k}^{n} T_j` and
the [time change](growth-time.md) `G`. Let `τ` be a random block-size history (a random list of
block-size lists) such that every preimage `τ⁻¹(A)` is measurable, with the
[random-joining law](../expected-site-frequency-spectrum/random-joining.md) from `n` singletons,
`μ(τ = ps) = R_{n-1}((1, …, 1), ps)` for every `ps` (with `n - 1` truncated at `0`: for `n = 0`,
`R_0` starts from the empty list); no independence is assumed. Then for every natural number
`i` the
[total length of the branches subtending `i` sample copies](../expected-site-frequency-spectrum/sfs-length.md)
for the holding times `T^ρ_k`,

`L^ρ_i = ∑_{k=2}^{n} c_{k,i} T^ρ_k`,

is square integrable, where `c_{k,i}` is the number of blocks of size `i` in entry `n - k` of
`τ` (the empty list if `τ` is shorter).
