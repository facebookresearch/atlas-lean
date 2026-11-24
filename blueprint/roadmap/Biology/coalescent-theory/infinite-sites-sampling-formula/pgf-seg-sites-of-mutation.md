# Probability generating function of the number of segregating sites

Let `μ` be a probability measure and let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) of a
sample of size `n` under `μ`: for `2 ≤ k ≤ n`, `T_k` has the exponential law with rate `C(k, 2)`,
and `T_2, …, T_n` are independent. Let `θ ≥ 0` and let `N = (N_b)` be natural-number counts on the
[branches](../poisson-mutation-on-the-kingman-genealogy/kingman-branch.md) of the genealogy whose
conditional law given the epoch-length vector `E = (T_2, …, T_n)` is the
[Kingman mutation kernel](../poisson-mutation-on-the-kingman-genealogy/kingman-mutation-kernel.md):
given `E`, independent Poisson counts with means `(θ / 2) max(T_k, 0)` on the `k` branches of epoch
`k`. Then the number of segregating sites `S = ∑_b N_b` satisfies, for every real `s` with
`|s| ≤ 1`, with natural powers and `0^0 = 1` (so that at `s = 0` the left side is `P(S = 0)`),

`E[s^S] = ∏_{k=1}^{n-1} k / (k + θ (1 - s))`.
