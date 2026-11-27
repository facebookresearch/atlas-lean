# Case-control sampling law

Let `μ` be a measure on `Ω`, `L` a real function on `Ω`, `t` a real threshold and `P` a real case
fraction. Write `C = {t ≤ L}` for the cases and `k = μ(C)` for their mass as a real number (`k = 0`
if `μ(C)` is infinite). The case-control law is the measure

`μ_cc = (P / k)⁺ · μ|_C + ((1 - P) / (1 - k))⁺ · μ|_{Cᶜ}`,

where `μ|_A` is `μ` restricted to `A` and `x⁺ = max(x, 0)`. When `μ` is a probability measure, `L`
is measurable, `0 < k < 1` and `0 ≤ P ≤ 1`, it is a
[probability measure](is-probability-measure-case-control.md) in which the cases have
[mass `P`](measure-real-case-case-control.md) and the controls `1 - P`, and the conditional laws
within cases and within controls are those of `μ`: the law of a case-control sample with case
fraction `P`. Outside that range the weights change: with the convention `x / 0 = 0` the case weight
is `0` when `k = 0` and the control weight is `0` when `k = 1`, and a negative weight (for example
the control weight when `P > 1` and `k < 1`) is replaced by `0`.
