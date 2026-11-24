# Triple and double mergers are negligible under Möhle–Sagitov

Let the sequence of [Cannings models](../cannings-models/cannings-model.md) `W_N` satisfy the
[Möhle–Sagitov conditions](mohle-sagitov.md) (`c_N > 0` for all large `N`, `c_N → 0` and
`μ_3 / (N² c_N) → 0`), with [pair-coalescence probabilities](pair-coalescence.md) `c_N` and third
[factorial moments](factorial-moment.md) `μ_3` of the offspring numbers. Then

`(p_3(N) + D_N) / c_N → 0` as `N → ∞`,

where `p_3(N) = N μ_3 / (N)_3` is the [triple-coalescence probability](triple-coalescence.md) and
`D_N = E[X²] / (N)_4` the [double-merger bound](double-bound.md) of `W_N`, with `X` the
[pair count](pair-count.md) of the parent map, `(N)_3 = N (N - 1) (N - 2)` and
`(N)_4 = N (N - 1) (N - 2) (N - 3)`. Triple mergers and simultaneous mergers of two disjoint pairs
are thus negligible on the time scale `1 / c_N`; the bound on simultaneous mergers follows from the
triple-merger condition, without a condition of its own.

The displayed quantities are defined for every `N`: `p_3(N) = 0` for `N < 3` and `D_N = 0` for
`N < 4`, where `(N)_3` or `(N)_4` is `0`, and at an `N` with `c_N = 0` (for instance `N ≤ 1`) the
quotient is `0`, all by the convention `x / 0 = 0`; this does not affect the limit.
