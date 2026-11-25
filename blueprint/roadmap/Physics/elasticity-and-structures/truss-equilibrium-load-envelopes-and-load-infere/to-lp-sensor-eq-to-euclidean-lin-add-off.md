# Sensor reading of a truss under a parametrized load

Let `J` and `M` be finite sets, with joint positions `r_j` in the plane, member `e` joining joint
`a_e` to joint `b_e`, a matrix `S` from `n_f` free coordinates to the joint displacement coordinates
and member weights `k`, such that the supported stiffness `K = (B S)ᵀ diag(k) (B S)` is positive
definite, `B` being the separation-form
[compatibility matrix](../pin-jointed-trusses/axial-compatibility.md). Let `C` be an `n_m × n_f`
sensor matrix, `B_load` an `n_f × n_p` load matrix and `f₀` a known load on the free coordinates,
and let `H = C K⁻¹ B_load` be the
[load observation matrix](../pin-jointed-trusses/load-observation-matrix.md).

If a displacement `u` on the free coordinates solves `K u = f₀ + B_load θ` for a load-parameter
vector `θ ∈ ℝ^{n_p}`, then the sensor reading is `C u = H θ + C K⁻¹ f₀`: the observation matrix
applied to `θ` plus the deterministic offset of the known load `f₀`.
