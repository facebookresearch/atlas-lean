# Scaling obstruction for separate parameters

Let `V > 0`, `CL ≥ 0` and `s > 0` with `s ≠ 1`. Scaling `V` and `CL` by the same `s` leaves the
normalized washout unchanged at every time, `exp (-((s * CL) / (s * V)) * t) = exp (-(CL / V) * t)`
for every real `t`, while the volume changes, `s * V ≠ V`. Hence normalized observations do not
identify the volume `V`, nor the pair `(V, CL)`, separately from the ratio `CL / V`. Zero clearance
is the exceptional boundary: at `CL = 0` the scaling fixes `CL`, and the constant washout `1` forces
`CL = 0`, so no non-identifiability of `CL` alone is claimed there.
