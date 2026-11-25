# Total AUC after a bolus is the dose over the clearance

For a clearance `CL > 0`, a volume `V > 0` and every real dose `D`, the total area under the bolus
[concentration](concentration-bolus.md) `C(t) = (D / V) * exp (-(CL / V) * t)` after a dose `D` with
no infusion is `∫₀^∞ C(t) dt = D / CL` (Gibaldi and Perrier).
