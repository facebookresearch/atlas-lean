# Tajima's variance estimator is unbiased under Poisson mutation marking

Let `n ≥ 2`, let `μ` be a probability measure and let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) of a
sample of size `n` under `μ`: for `2 ≤ k ≤ n`, `T_k` has the exponential law with rate `C(k, 2)`,
and `T_2, …, T_n` are independent. Suppose the [epoch-length vector](epochs.md)
`E = (T_2, …, T_n)` is measurable. Let `θ ≥ 0` and let `N = (N_b)` be natural-number counts on
the [branches](kingman-branch.md) of the genealogy whose conditional law given `E` is the
[Kingman mutation kernel](kingman-mutation-kernel.md): given `E`, independent Poisson counts with
means `(θ / 2) max(T_k, 0)` on the `k` branches of epoch `k`. Then the number of segregating
sites `S = ∑_b N_b` satisfies

`E[e_1 S + e_2 S (S - 1)] = c_1 θ + c_2 θ²`

(Tajima 1989), with
[Tajima's constants](../segregating-sites-and-pairwise-differences/tajima-e1.md) `c_1`, `c_2`,
`e_1 = c_1 / a_1` and `e_2 = c_2 / (a_1² + a_2)` of the sample size `n`.
