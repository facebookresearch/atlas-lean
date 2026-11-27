# Peak altitude selected on an altitude band

For real numbers `ρ₀`, `H`, `β`, `γ`, `h_min` and `h_e`, the peak altitude selected on the band
`[h_min, h_e]` is the [candidate peak altitude](peak-deceleration-altitude.md)
`h* = H log(2 K)` clamped to the band,

`max(h_min, min(h*, h_e))`.

For `h_min < h_e` it is `h*` when `h*` lies in the band, `h_min` when `h* < h_min` and `h_e` when
`h* > h_e`; for `h_min ≥ h_e` it is `h_min`. For `ρ₀, H, β, v_e > 0`, `sin γ > 0` and
`h_min < h_e` it [maximizes the deceleration](is-max-on-band-peak-altitude.md) on the band.
