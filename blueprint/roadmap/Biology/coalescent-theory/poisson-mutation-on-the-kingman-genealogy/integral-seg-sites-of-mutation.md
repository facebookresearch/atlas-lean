# Expected number of segregating sites under Poisson mutation marking

Let `μ` be a probability measure and let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) of a
sample of size `n` under `μ`: for `2 ≤ k ≤ n`, `T_k` has the exponential law with rate `C(k, 2)`,
and `T_2, …, T_n` are independent. Suppose the [epoch-length vector](epochs.md)
`E = (T_2, …, T_n)` is measurable. Let `θ ≥ 0` and let `N = (N_b)` be natural-number counts on
the [branches](kingman-branch.md) of the genealogy whose conditional law given `E` is the
[Kingman mutation kernel](kingman-mutation-kernel.md): given `E`, independent Poisson counts with
means `(θ / 2) max(T_k, 0)` on the `k` branches of epoch `k`. Then the number of segregating
sites `S = ∑_b N_b` has mean

`E[S] = θ H_{n-1}`,

where `H_m = ∑_{j=1}^{m} 1 / j` is the harmonic number and `n - 1` is a natural-number
difference; for `n ≤ 1` both sides are `0`. The integrability and conditional mean that
[the expected number of segregating sites](../kingman-s-coalescent-and-watterson-s-estimator/integral-seg-sites.md)
assumes come here from the mutation model.
