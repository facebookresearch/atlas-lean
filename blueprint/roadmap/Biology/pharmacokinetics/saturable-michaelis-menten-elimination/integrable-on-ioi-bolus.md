# The bolus AUC is finite

For `Vmax, Km > 0` and `C(0) ≥ 0`, a bolus solution is
integrable on `(0, ∞)`. (This makes `IsSolution.integral_Ioi_bolus` a statement about a
convergent integral, not the Bochner default `0`.)
