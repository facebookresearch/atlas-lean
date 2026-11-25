# Stream function of the flow past a cylinder with circulation

For real `U`, `a`, `Γ`, `x`, `y`, with `r = √(x² + y²)`, the stream function is
`ψ(x, y) = U(y − a²y/r²) − (Γ/(2π)) log(r/a)`, a single-valued real function: no complex logarithm
or branch choice enters. It is meant for `a > 0` and `r > 0`; the flow region is `r ≥ a`. With the
conventions that division by zero gives `0`, `log 0 = 0` and `log s = log |s|` for `s < 0`: at the
origin `ψ(0, 0) = 0`; for `a = 0` the logarithmic term vanishes and `ψ = Uy`; and for `a < 0` the
logarithm is `log(r/|a|)`, so `ψ` is the same as for `|a|`.

For `a > 0` and `(x, y) ≠ (0, 0)` it generates the velocity of the flow past the cylinder:
`∂ψ/∂y = u` ([derivative in y](cyl-stream-deriv-y.md)) and `∂ψ/∂x = −v`
([derivative in x](cyl-stream-deriv-x.md)), where `u` and `v` are the [horizontal](cyl-u.md) and
[vertical](cyl-v.md) velocities.
