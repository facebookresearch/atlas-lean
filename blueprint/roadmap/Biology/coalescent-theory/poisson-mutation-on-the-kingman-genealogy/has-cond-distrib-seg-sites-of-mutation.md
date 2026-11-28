# The number of segregating sites is conditionally Poisson

Let `μ` be an s-finite measure and let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) of a
sample of size `n` under `μ`: for `2 ≤ k ≤ n`, `T_k` has the exponential law with rate `C(k, 2)`,
and `T_2, …, T_n` are independent. Let `θ ≥ 0` and let `N = (N_b)` be natural-number counts on the
[branches](kingman-branch.md) of the genealogy whose conditional law given the
[epoch-length vector](epochs.md) `E = (T_2, …, T_n)` is the
[Kingman mutation kernel](kingman-mutation-kernel.md): the pair `(E, N)` is `μ`-almost everywhere
measurable, and the image of `μ` under `(E, N)` is the composition product of the image of `μ` under
`E` with the kernel of independent Poisson counts with means `(θ / 2) max(T_k, 0)` on the `k`
branches of epoch `k`. Then the number of segregating sites `S = ∑_b N_b` has, in the same sense,
conditional law

`Po((θ / 2) ∑_b ℓ_b(E))` given `E`,

where `ℓ_b(E) = max(T_k, 0)` for the branches `b` of epoch `k`. This is the case of the
[total of independent Poisson branch counts](has-cond-distrib-sum-of-branch-mutation.md) with the
Kingman genealogy.
