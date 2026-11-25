# Saturable-elimination equation under constant infusion

For real numbers `Vmax`, `Km` and `R`, a function `C` of time solves the saturable-elimination
equation when, at every time `t ≥ 0`, it is differentiable at `t` (with a two-sided derivative, also
at `t = 0`) and `C'(t) = R - Vmax * C(t) / (Km + C(t))`: constant infusion at the rate `R` and
Michaelis–Menten elimination with maximal rate `Vmax` and Michaelis constant `Km`. The equation is
stated for all real parameters, with the convention `x / 0 = 0`: where `C(t) = -Km` the elimination
rate is `0`. In the model `Vmax > 0`, `Km > 0`, `R ≥ 0` and `C(0) ≥ 0`, and the solution then
[stays nonnegative](nonneg.md).
