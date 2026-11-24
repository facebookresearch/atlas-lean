# Variance of a linear combination of branch lengths

Let `μ` be a probability measure on a measurable space `Ω` and `n` a natural number. Let `(T_k)`
be [Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) of a sample of size `n` under `μ`: for
`2 ≤ k ≤ n`, `T_k` is exponential with rate `C(k, 2)`, and `T_2, …, T_n` are mutually independent.
Let `τ` be a random list of block-size lists such that every preimage `τ⁻¹(S)` is measurable, with
the [random-joining law](../expected-site-frequency-spectrum/random-joining.md) from `n` singletons,
`μ(τ = p) = R_{n-1}((1, …, 1), p)` for every `p`, and such that `τ` and the family `(T_k)_{k ∈ ℕ}`
are independent under `μ`. Here `(1, …, 1)` has `n` entries and `n - 1` is natural subtraction:
for `n = 0` the initial list is empty, no step is taken, and the law is concentrated on the
history whose only entry is the empty list. Let
`L_i = ∑_{k=2}^{n} c_i(τ_{n-k}) T_k` be the
[total length of the branches subtending exactly `i` sample copies](../expected-site-frequency-spectrum/sfs-length.md), where
`c_i(τ_{n-k})` is the number of entries equal to `i` in the entry of index `n - k` of `τ` (the
block sizes while `k` lineages remain; the empty list if there is no such entry).
Then for all real numbers `c_i`,

`Var(∑_{i=1}^{n-1} c_i L_i) = 4 ∑_{i=1}^{n-1} ∑_{j=1}^{n-1} c_i c_j σ_{ij}`,

where `σ_{ij}` is [Fu's closed form](../fu-s-covariances-of-the-site-frequency-spectrum/fu-sigma.md) (Fu 1995).
For `n ≤ 1` these sums are empty and both sides are `0`.
