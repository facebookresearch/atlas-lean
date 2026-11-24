# Absolute bolus reconstruction

Exact noiseless bolus observations
`C₀ = D / V` at time `0` and `Ct = (D / V) * exp (-(CL / V) * t)` at time
`t > 0`, with known dose `D > 0`, volume `V > 0` and clearance `CL ≥ 0`,
recover the volume, the elimination rate and the clearance. The two
formulas are `concentration_bolus` at times `0` and `t`. This is a
statement about the model only; it is no finite-sample estimator
guarantee and no fit to an individual. The `CL ≥ 0` hypotheses state the
physical domain; the algebra itself needs less, hence the local linter
suppression on the statements.
