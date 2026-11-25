# The flux of an ohmic density is σ times the field flux

For every real `σ`, parameter domains `D_f ⊆ ℝ²` and field components `E_f : ℝ² → ℝ` on the six
faces, the [flux](face-flux.md) of the [ohmic density](ohmic-density.md) `σ E_f` through face `f` is
`σ` times the flux of `E_f`:

`∫_{D_f} σ E_f(p) dp = σ ∫_{D_f} E_f(p) dp`.

No integrability is assumed: when `E_f` is not integrable on `D_f`, both sides are `0`.
