# Concentration after a bolus

For all real `CL`, `V`, `D` and `t`, the [concentration](concentration.md) after a bolus dose `D`
with no infusion is `C(t) = (D / V) * exp (-k * t)` with `k = CL / V`. With the convention
`x / 0 = 0` both sides are `0` when `V = 0`; in the model `V > 0` and `CL ≥ 0`.
