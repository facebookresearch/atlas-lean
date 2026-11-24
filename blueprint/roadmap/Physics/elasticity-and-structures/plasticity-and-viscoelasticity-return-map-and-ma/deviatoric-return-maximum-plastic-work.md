# Deviatoric return maximum plastic work

Maximum plastic work for the deviatoric return. For a trial stress `σTrial`, a shear modulus
`μ > 0` and a fixed nonempty complete convex yield section `K` of symmetric trace-free stresses,
let `σ := meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial)` be the returned
stress and
`Δε_p := (σTrial - σ) / (2 μ)` the isotropic plastic strain increment. Then every admissible
stress `τ ∈ K` satisfies `(σ - τ) : Δε_p = ∑ i, ∑ j, (σ - τ) i j * Δε_p i j ≥ 0`: for
every admissible comparison stress `τ ∈ K`, the returned stress `σ` (which itself need not
lie in `K`, since it carries the trial mean stress) does at least as much plastic work on
`Δε_p` as `τ`. The hydrostatic
part of `σ` does no plastic work because `Δε_p` is trace-free, which uses `K ⊆ deviatoricStresses`
(pressure insensitivity). No symmetry of `σTrial` is needed.
