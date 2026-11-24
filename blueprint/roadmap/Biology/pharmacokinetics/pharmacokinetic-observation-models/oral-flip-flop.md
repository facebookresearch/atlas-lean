# Flip-flop parameter transformation

For positive `V`, `ka` and `CL` with distinct rates `ka ≠ CL / V`, a bioavailability `F ≥ 0` and all
real `D` and `t`, let
`C(t) = F * D * ka * (exp (-(CL / V) * t) - exp (-ka * t)) / (V * (ka - CL / V))` be the oral
concentration curve of the tuple `(F, D, ka, V, CL)`. If `F * ka / (CL / V) ≤ 1`, then `C(t)` equals
the oral curve of the flipped tuple `(F * ka / (CL / V), D, CL / V, V, ka * V)`, and the flipped
bioavailability `F * ka / (CL / V)` is nonnegative. The flip exchanges the absorption rate `ka` and
the elimination rate `CL / V`, keeps the dose and the volume, and transforms the bioavailability
rather than keeping it. The condition `F * ka / (CL / V) ≤ 1`, which makes the flipped
bioavailability admissible, is a hypothesis; the transformed tuple is shown to give the same curve,
with no claim that it is the only one. Equal rates are excluded: the denominator vanishes there, and
the limiting equal-rate curve has another form.
