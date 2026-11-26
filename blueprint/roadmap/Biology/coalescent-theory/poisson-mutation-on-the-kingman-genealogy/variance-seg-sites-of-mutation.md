# Variance of the segregating-site count under Poisson mutation marking

Let `μ` be a probability measure and let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) of a
sample of size `n` under `μ`: for `2 ≤ k ≤ n`, `T_k` has the exponential law with rate `C(k, 2)`,
and `T_2, …, T_n` are independent. Suppose the [epoch-length vector](epochs.md)
`E = (T_2, …, T_n)` is measurable. Let `θ ≥ 0` and let `N = (N_b)` be natural-number counts on
the [branches](kingman-branch.md) of the genealogy whose conditional law given `E` is the
[Kingman mutation kernel](kingman-mutation-kernel.md): given `E`, independent Poisson counts with
means `(θ / 2) max(T_k, 0)` on the `k` branches of epoch `k`. Then the number of segregating
sites `S = ∑_b N_b` has variance

`Var(S) = θ a_1 + θ² a_2`, with `a_1 = ∑_{i=1}^{n-1} 1 / i` and `a_2 = ∑_{i=1}^{n-1} 1 / i²`

(Watterson 1975); for `n ≤ 1` both sides are `0`.
