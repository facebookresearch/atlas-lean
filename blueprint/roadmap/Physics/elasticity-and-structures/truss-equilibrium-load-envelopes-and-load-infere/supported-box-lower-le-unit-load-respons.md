# Lower envelope bound for supported truss loads in a box

Let `J` (joints), `M` (members) and `F` (free coordinates) be finite sets, with joint positions
`r_j` in the plane, member `e` joining joint `a_e` to joint `b_e`, a matrix `S` from the free
coordinates to the joint displacement coordinates, member weights `k` and a fixed output functional
`aout` on `F`. The [influence vector](../pin-jointed-trusses/influence-vector.md) is `η = K⁻¹ aout`
for the supported stiffness `K = (B S)ᵀ diag(k) (B S)`, `B` being the separation-form
[compatibility matrix](../pin-jointed-trusses/axial-compatibility.md), and the
[unit-load response](../pin-jointed-trusses/unit-load-response.md) of a load `f` on the free
coordinates is `η · f`.

Then every load `f` with `0 ≤ f_i ≤ cap_i` for all free coordinates `i` has unit-load response
`η · f ≥ ∑_i cap_i * min(η_i, 0)`. No positivity of the weights and no definiteness of `K` is
assumed: the inverse of a singular matrix is the zero matrix by convention, so that `η = 0` and
every response is `0` when `K` is singular. The physical reading is a positive definite `K`.
