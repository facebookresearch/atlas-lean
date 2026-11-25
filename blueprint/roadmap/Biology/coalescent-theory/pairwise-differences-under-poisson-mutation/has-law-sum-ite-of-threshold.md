# Epoch sum above a threshold with $P(M \le k) = p_{n,k}$ is Exp(1)

Let `n ≥ 2`, let `𝓗` be a finite set in which every subset is measurable, let `ν` be a
probability measure on `𝓗`, and let `A(h, k)` be a property of `h ∈ 𝓗` and natural numbers `k`
such that, for every `h`, `A(h, 1)` fails, `A(h, n)` holds, and `A(h, k)` implies `A(h, k + 1)`
for `1 ≤ k < n`. So on `{1, …, n}` the `k` with `A(h, k)` form `{M(h), …, n}` for a threshold
`2 ≤ M(h) ≤ n`. Suppose that for every `1 ≤ k ≤ n`

`ν{h : A(h, k)} = (k - 1)(n + 1) / ((n - 1)(k + 1))`,

that is, `ν{M ≤ k} = p_{n,k}` in the notation of the
[probability that a pair lies in separate lineages](../segregating-sites-and-pairwise-differences/pair-separate-prob.md).

Then under the product of the
[holding-time law](../kingman-s-coalescent-and-watterson-s-estimator/pi-measure.md)
`⊗_{k=2}^n Exp(C(k, 2))` and `ν`, that is, for independent epoch lengths `t_k` exponential with
rate `C(k, 2)` and an independent `h` with law `ν`, the sum of the `t_k` over the `2 ≤ k ≤ n`
with `A(h, k)` has the exponential law with rate `1`.

Conditionally on `h`, the characteristic function of the sum at `u` is
`∏_{k : A(h, k)} C(k, 2) / (C(k, 2) - i u)`. Since `A(h, ·)` is a threshold, this product equals
`∑_{m=2}^n (1[A(h, m)] - 1[A(h, m - 1)]) ∏_{k=m}^n C(k, 2) / (C(k, 2) - i u)`, which is linear
in the indicators; averaging over `ν` and applying the [mixture identity](sum-pair-ratio-prod.md)
gives `1 / (1 - i u)`, the characteristic function of `Exp(1)`.
