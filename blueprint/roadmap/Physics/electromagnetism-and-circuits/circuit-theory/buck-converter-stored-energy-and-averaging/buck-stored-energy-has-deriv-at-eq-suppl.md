# Between switches the buck energy changes at supplied power minus loss

Let `L > 0`, `C > 0`, `R > 0` and `Vin` be real numbers, `s, i, v : ℝ → ℝ` functions of time and `t`
a time at which `i` and `v` are differentiable and the inductor and capacitor laws
`L i'(t) = s(t) Vin - v(t)` and `C v'(t) = i(t) - v(t) / R` hold. Then the
[stored energy](buck-stored-energy.md) has derivative `s(t) Vin i(t) - v(t)² / R` at `t`: the
switched input power minus the resistive loss.
