# Heavy tails mean a positive triple-merger rate

Under the [Möhle–Sagitov conditions](mohle-sagitov-lambda.md) for a sequence of Cannings models and
a finite measure `Λ` on `[0, 1]`, the [heavy-tail condition](heavy-tailed.md) holds if and only if
the limiting triple-merger rate `λ_{3,3} = ∫ x Λ(dx)` is positive. The condition used is
`q_3 / c_N → ∫ x Λ(dx)`, with `q_3` the probability that three sampled lineages share a parent and
`c_N` the coalescence probability; the heavy-tail condition asks for a positive limit of
`q_3 / c_N`. At an `N` with `c_N = 0` (for instance `N ≤ 1`) the ratio `q_3 / c_N` is `0`, by the
convention `x / 0 = 0`; the limits depend only on large `N`, where `c_N > 0`.
