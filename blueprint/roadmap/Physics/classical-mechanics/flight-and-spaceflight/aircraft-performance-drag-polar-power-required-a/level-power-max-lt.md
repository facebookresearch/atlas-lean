# Every other speed above stall needs more power than max(V_s, V_mp)

Let `W > 0` and `ρ, S, CD0, k, CLmax > 0`, and let `V* = max(V_s, V_mp)`, with
[stall speed](stall-speed.md) `V_s = √(2 W / (ρ S CLmax))` and `V_mp` the
[minimum-power speed](min-power-speed.md). Every speed `V > 0` with lift coefficient
`CL(V) = 2 W / (ρ V² S) ≤ CLmax` and `V ≠ V*` needs strictly more power than `V*`: `P(V*) < P(V)`
for the [power required](level-power.md) `P(V) = D(V) V`. When `V_mp < V_s`, `V*` is the stall
speed, not the unconstrained minimizer.
