# Second moments of the holding times

Let `μ` be a probability measure and let `T_k` (`k ∈ ℕ`) be [Kingman holding times](kingman-times.md)
of a sample of size `n` under `μ`: for `2 ≤ k ≤ n`, `T_k` has the exponential law with rate
`C(k, 2)`, and `T_2, …, T_n` are independent. For all `k` and `k'` with `2 ≤ k, k' ≤ n`,

`E[T_k T_{k'}] = 1 / (C(k, 2) C(k', 2)) + δ_{kk'} / C(k, 2)²`:

`E[T_k²] = 2 / C(k, 2)²` by the exponential law, and `E[T_k T_{k'}] = E[T_k] E[T_{k'}]` for
`k ≠ k'` by independence.
