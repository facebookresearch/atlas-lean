# Finite-horizon AUC

For a clearance `CL > 0`, a volume `V > 0`, every real dose `D` and every real `T`, the bolus
[concentration](concentration-bolus.md) `C(t) = (D / V) * exp (-(CL / V) * t)` after a dose `D` with
no infusion satisfies `∫₀ᵀ C(t) dt = (D / CL) * (1 - exp (-k * T))` with `k = CL / V`; for `T < 0`
the integral is oriented, `∫₀ᵀ C(t) dt = -∫_T^0 C(t) dt`.
