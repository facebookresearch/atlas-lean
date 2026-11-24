# Concentration in a well-mixed ventilated room

For real `V`, `Q`, `c_out`, `G`, `c₀` and `t`, the ventilation concentration is the one-compartment
[relaxation](../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/relaxation.md)
at exchange rate `Q/V` and constant input `(Q c_out + G)/V`:

`c(t) = c₀ e^{-(Q/V)t} + ∫_0^t e^{-(Q/V)(t - s)} (Q c_out + G)/V ds`,

the solution of `c′ = (Q/V)(c_out - c) + G/V` with `c(0) = c₀` for a room of volume `V`, flow `Q`,
outdoor concentration `c_out` and indoor source `G`. With `x/0 = 0`, it is the constant `c₀` when
`V = 0`. In the physical reading `V > 0` and `Q > 0`.
