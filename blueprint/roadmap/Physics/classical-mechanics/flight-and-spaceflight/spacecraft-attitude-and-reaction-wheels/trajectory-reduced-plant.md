# The trajectory solves the reduced wheel plant

For `I, k > 0` and `|ω₀| ≤ U_max / k`:
`ω(0) = ω₀` and `h_w(0) = h₀`, and at every `t ≥ 0` the rate has the closed-loop derivative
`ω' = τ_b(ω) / I`, the wheel momentum has the derivative `h_w' = u_w`, and `I ω' = τ_ext - u_w`
with `τ_ext = 0`. These are the body and wheel equations of `AttitudePorts`: the locked body's
momentum changes at the rate `-u_w` and the wheel's at the rate `u_w`.
