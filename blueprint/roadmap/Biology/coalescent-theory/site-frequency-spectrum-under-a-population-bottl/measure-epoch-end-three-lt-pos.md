# The oldest epoch can start before c and outlast a

Let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md)
of a sample of size `n` under a measure `μ` on `Ω`: for `2 ≤ k ≤ n`, `T_k` has the exponential
law with rate `C(k, 2)` under `μ`, and `T_2, …, T_n` are independent.
Let `n ≥ 2` and let `a` and `c` be real numbers with `0 ≤ a < c`. With
`V_3 = ∑_{j=3}^{n} T_j` (`0` when `n = 2`), the event `{V_3 < c and T_2 > a}` has positive
`μ`-probability (`μ` is a probability measure, since `n ≥ 2`): the epoch with two lineages can
start before standard time `c` and last longer than `a`. The event contains
`{T_2 > a} ∩ ⋂_{3 ≤ j ≤ n} {T_j ≤ c / n}`, whose probability is positive by independence of the
holding times.
