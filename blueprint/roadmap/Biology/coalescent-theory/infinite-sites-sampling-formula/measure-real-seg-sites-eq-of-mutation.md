# The infinite-sites sampling formula

Let `n ≥ 2`, let `μ` be a probability measure and let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) of a
sample of size `n` under `μ`: for `2 ≤ k ≤ n`, `T_k` has the exponential law with rate `C(k, 2)`,
and `T_2, …, T_n` are independent. Let `θ ≥ 0` and let `N = (N_b)` be natural-number counts on
the [branches](../poisson-mutation-on-the-kingman-genealogy/kingman-branch.md) of the genealogy
whose conditional law given the epoch-length vector `E = (T_2, …, T_n)` is the
[Kingman mutation kernel](../poisson-mutation-on-the-kingman-genealogy/kingman-mutation-kernel.md):
given `E`, independent Poisson counts with means `(θ / 2) max(T_k, 0)` on the `k` branches of
epoch `k`. Then the number of segregating sites `S = ∑_b N_b` has, for every natural number `m`,

`P(S = m) = (n - 1) ∑_{j=0}^{n-2} (-1)^j C(n - 2, j) θ^m / (θ + j + 1)^{m+1}`,

[Tavaré's formula](seg-sites-prob.md) (Watterson 1975, Tavaré 1984). Powers are natural powers with
`θ^0 = 1`, also at `θ = 0`, where all the mass is at `m = 0`.
