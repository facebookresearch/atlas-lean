# Thermal wind balance

**Thermal wind balance** from hydrostatic balance of a pressure field (f-plane, Boussinesq).
On `Space 3` with coordinates east, north and up, let the `C²` pressure `p` and the density `ρ`
satisfy hydrostatic balance `∂p/∂z = -ρ g`, and let the velocity `(u, v)` satisfy geostrophic
balance `f u = -(1/ρ₀) ∂p/∂y`, `f v = (1/ρ₀) ∂p/∂x` with `f ≠ 0` and `ρ₀ ≠ 0`. Then
`f ∂u/∂z = (g/ρ₀) ∂ρ/∂y` and `f ∂v/∂z = -(g/ρ₀) ∂ρ/∂x`: the horizontal density gradient
determines the vertical shear of the geostrophic wind. Unlike `thermal_wind`, the commuted
mixed partial derivatives of `p` are derived from `C²` regularity, not assumed.
