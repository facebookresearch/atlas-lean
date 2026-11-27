# Deviatoric return

Deviatoric return map with isotropic corrector. For a symmetric trial stress `σTrial`, a
shear modulus `μ > 0` and a fixed nonempty complete convex yield section `K` of symmetric
trace-free stresses, put `s := convexProjection K (deviatoricStress σTrial)` and
`σ := meanStress σTrial • 1 + s`. Then the trial deviator is symmetric trace-free, `s ∈ K`, the
returned stress `σ` is symmetric with the trial mean stress and deviator `s`, the plastic strain
increment `(σTrial - σ) / (2 μ)` equals `(deviatoricStress σTrial - s) / (2 μ)` and is symmetric
trace-free (no volumetric plastic strain), `σ = σTrial - 2 μ Δε_p`, and a trial deviator already
in `K` gives zero correction.
