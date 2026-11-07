# The general Green kernel specializes to Kimura's sojourn density

For genic selection
`b x = σ x (1 - x)`, `a x = x (1 - x)`, the general Green's function `greenFunction` is
`selectionGreen σ` on `[0, 1] × (0, 1)`. The scale function is `S(y) = u(y) / u'(0)` with
`u = kimuraFixation σ` and `u'(0) = kimuraSlope σ`, since both have derivative `ψ(y) = e^{-2σy}`
and vanish at `0`; substituting that and `S(1) = 1 / u'(0)` into `greenFunction` gives
`selectionGreen`.
