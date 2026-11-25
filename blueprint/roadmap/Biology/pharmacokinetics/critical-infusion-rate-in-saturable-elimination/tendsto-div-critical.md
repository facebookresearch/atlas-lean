# Sublinear growth at the critical rate

Let `Vmax > 0` and `Km > 0`, and let `C` be differentiable at every time `t ≥ 0` with
`C'(t) = Vmax - Vmax * C(t) / (Km + C(t))`, saturable elimination under the critical infusion rate
`R = Vmax`, starting at `C(0) ≥ 0`.

Then `C(t) / t → 0` as `t → ∞`: the accumulation at the critical rate is slower than every linear
rate. For an infusion rate `R > Vmax`, by contrast, a solution with `C(0) ≥ 0` grows at least
linearly: `C(t) ≥ C(0) + (R - Vmax) t` for every `t ≥ 0`
([zero-order lower bound](../saturable-michaelis-menten-elimination/add-mul-le.md)).
