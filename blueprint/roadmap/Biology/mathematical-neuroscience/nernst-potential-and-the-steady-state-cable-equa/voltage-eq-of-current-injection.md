# Bounded response to current injection into a semi-infinite cable

Let `r_m > 0` and `r_i > 0`, and let `V` and `I` be a [steady state](../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/is-steady-state.md) of the passive cable on `[0, ∞)`
(derivatives within `[0, ∞)`) whose voltage is bounded on `[0, ∞)`, with injected current
`I(0) = I₀`. Then for every `x ≥ 0`

`V(x) = r∞ I₀ e^(-x / λ)`,

where `λ = √(r_m / r_i)` is the [length constant](../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/length-constant.md) and `r∞ = √(r_m r_i)` the [characteristic resistance](../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/char-resistance.md): the input resistance of the
semi-infinite cable is `r∞`.
