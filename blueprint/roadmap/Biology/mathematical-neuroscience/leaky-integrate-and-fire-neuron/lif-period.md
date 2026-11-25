# Period of the leaky integrate-and-fire neuron

For real `τ`, `u_r`, `θ` and `u_∞`, the period is `T = τ log((u_∞ - u_r)/(u_∞ - θ))`. For `τ > 0`
and superthreshold drive `u_r < θ < u_∞` it is [positive](lif-period-pos.md), and it is the first
time at which the voltage `u(t) = u_∞ - (u_∞ - u_r) e^(-t/τ)` reaches the threshold `θ`
([first hit](lif-first-hit.md)).

Outside that domain the formula follows the conventions `x / 0 = 0`, `log 0 = 0` and
`log x = log |x|`; for example it is `0` when `u_∞ = θ`. In the model the time constant `τ` is
positive and the refractory period `t_ref` nonnegative.
