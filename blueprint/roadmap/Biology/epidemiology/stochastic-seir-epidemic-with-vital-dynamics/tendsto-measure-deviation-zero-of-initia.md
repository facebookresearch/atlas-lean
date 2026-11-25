# Deterministic initial counts with convergent scaled values satisfy Kurtz's initial condition

Let `P` be a measure on a space `Ω`, let `S_N, E_N, I_N, R_N` be count paths depending on `ω ∈ Ω`,
and let `s`, `e`, `i`, `r` be real functions. Suppose that for each `N`, almost surely,
`S_N(0) = S⁰_N`, `E_N(0) = E⁰_N`, `I_N(0) = I⁰_N` and `R_N(0) = R⁰_N` for natural numbers `S⁰_N`,
`E⁰_N`, `I⁰_N`, `R⁰_N`, and that `S⁰_N / N → s(0)`, `E⁰_N / N → e(0)`, `I⁰_N / N → i(0)` and
`R⁰_N / N → r(0)` as `N → ∞`. Then for every `δ > 0`,

`P(D_N(0) ≥ δ) → 0`  as `N → ∞`,

where `D_N` is the [deviation](deviation.md) of `(S_N, E_N, I_N, R_N) / N` from `(s, e, i, r)`: this
is the initial-condition hypothesis of [Kurtz's law of large numbers](tendsto-measure-deviation.md).
The measure `P` need not be a probability measure, and the event is not assumed measurable: `P` is
applied as an outer measure.
