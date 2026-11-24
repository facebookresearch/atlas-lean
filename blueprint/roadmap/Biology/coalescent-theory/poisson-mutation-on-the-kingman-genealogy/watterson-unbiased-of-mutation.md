# Watterson's estimator is unbiased under Poisson marking for n ≥ 2

Let `n ≥ 2`, let `μ` be a probability measure and let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) of a
sample of size `n` under `μ`: for `2 ≤ k ≤ n`, `T_k` has the exponential law with rate `C(k, 2)`,
and `T_2, …, T_n` are independent. Suppose the [epoch-length vector](epochs.md)
`E = (T_2, …, T_n)` is measurable. Let `θ ≥ 0` and let `N = (N_b)` be natural-number counts on
the [branches](kingman-branch.md) of the genealogy whose conditional law given `E` is the
[Kingman mutation kernel](kingman-mutation-kernel.md): given `E`, independent Poisson counts with
means `(θ / 2) max(T_k, 0)` on the `k` branches of epoch `k`. Then, with `S = ∑_b N_b` the number
of segregating sites and `H_{n-1} = ∑_{j=1}^{n-1} 1 / j`,

`E[S / H_{n-1}] = θ`

(Watterson 1975): `S` is the number of infinite-sites mutation events on the Kingman genealogy
at rate `θ / 2` per lineage.
