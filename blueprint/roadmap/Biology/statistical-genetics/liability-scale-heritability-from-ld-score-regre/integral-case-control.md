# Integrals under the case-control law

Let `μ` be a measure on `Ω` (not necessarily a probability measure), `L` a real function on `Ω`, `t`
a real threshold and `0 ≤ P ≤ 1`, and suppose that the cases `C = {t ≤ L}` have real mass
`k = μ(C) < 1` (`k = 0` if `μ(C)` is infinite). Then for every `μ`-integrable real function `f`, the
integral under the [case-control law](case-control.md) `μ_cc` is

`∫ f dμ_cc = (P / k) ∫_C f dμ + ((1 - P) / (1 - k)) ∫_{Cᶜ} f dμ`,

where with the convention `x / 0 = 0` the first term is `0` when `k = 0`.
