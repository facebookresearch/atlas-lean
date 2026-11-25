# A bounded steady state on the half-line decays as e^(−x/λ)

Let `r_m > 0` and `r_i > 0`, and let `V` and `I` be a [steady state](../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/is-steady-state.md) of the passive cable on the half-line
`[0, ∞)` (derivatives within `[0, ∞)`, one-sided at `0`) whose voltage is bounded: there is `M`
with `|V(x)| ≤ M` for every `x ≥ 0`. Then the input relation `V(0) = r∞ I(0)` holds, and for every
`x ≥ 0`

`V(x) = V(0) e^(-x / λ)` and `I(x) = I(0) e^(-x / λ)`,

where `λ = √(r_m / r_i)` is the [length constant](../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/length-constant.md) and `r∞ = √(r_m r_i)` the [characteristic resistance](../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/char-resistance.md).
