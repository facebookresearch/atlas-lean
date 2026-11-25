# The Beta-coalescent measure on the unit interval

For a real `α`, the measure on `[0, 1]` obtained by pushing forward, along the clamp
`x ↦ min(max(x, 0), 1)`, the measure on `ℝ` with density `x^{1-α} (1 - x)^{α-1} / B(2 - α, α)`
on `(0, 1)` and `0` elsewhere. For `0 < α < 2` it is the `Beta(2 - α, α)` law, a
[probability measure](is-probability-measure-beta-lambda.md), and its Λ-coalescent is the
Beta-coalescent; the density lives on `(0, 1)`, so the clamp changes nothing. For other `α` the
density is evaluated as written, with `B(a, b) = Γ(a) Γ(b) / Γ(a + b)`, where the real Gamma
function is given the value `0` at its poles `0, -1, -2, …`, with `1 / 0 = 0` and with negative
values read as `0`; the result need not be a probability measure: for `α = 2` it is the zero
measure.
