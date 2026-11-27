# Gaussian posterior of truss load parameters given sensor readings

Let `J` and `M` be finite sets, with joint positions `r_j` in the plane, member `e` joining joint
`a_e` to joint `b_e`, a matrix `S` from `n_f` free coordinates to the joint displacement coordinates
and member weights `k`, such that the supported stiffness `K = (B S)ᵀ diag(k) (B S)` is positive
definite, `B` being the separation-form
[compatibility matrix](../pin-jointed-trusses/axial-compatibility.md). Let `C` be an `n_m × n_f`
sensor matrix, `B_load` an `n_f × n_p` load matrix and `f₀` a known load on the free coordinates,
and let `H = C K⁻¹ B_load` be the
[load observation matrix](../pin-jointed-trusses/load-observation-matrix.md).

On a probability space, let `θ` (in `ℝ^{n_p}`) and the sensor noise `v` (in `ℝ^{n_m}`) be
independent measurable random vectors, with `θ ~ N(m, S_θ)` and `v ~ N(0, R)` for positive
semidefinite `S_θ` and `R`, and let the random displacement `u` solve `K u = f₀ + B_load θ` at every
outcome. Suppose that `H S_θ Hᵀ + R` is invertible. Then for almost every value `y` of the corrected
reading `C u + v - C K⁻¹ f₀`, with respect to its law, the conditional law of `θ` given the
corrected reading `y` is the Gaussian law with mean `m + S_θ Hᵀ (H S_θ Hᵀ + R)⁻¹ (y - H m)` and
covariance `S_θ - S_θ Hᵀ (H S_θ Hᵀ + R)⁻¹ H S_θ`. No identifiability of the load parameters is
assumed.
