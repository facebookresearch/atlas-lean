# Absolute bolus reconstruction

Let `D > 0` be a known dose, `V > 0` the volume, `CL ≥ 0` the clearance and `t > 0` a sampling time,
and let `C₀ = D / V` and `Ct = (D / V) * exp (-(CL / V) * t)` be the exact noiseless bolus
concentrations at times `0` and `t`. Then `C₀ > 0` and `Ct > 0`, and the observations recover the
volume, the elimination rate and the clearance: `V = D / C₀`, `CL / V = -log (Ct / C₀) / t` and
`CL = -(V / t) * log (Ct / C₀)`. This is a statement about the model only, not a finite-sample
estimator guarantee or a fit to an individual.
