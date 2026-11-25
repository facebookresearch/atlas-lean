# End forces of a uniformly loaded quartic from the stiffness matrix

Let `EI > 0` and `L > 0`, and let `y(x) = a + b x + c x² + d x³ + e x⁴` for all real `x` satisfy
`EI y''''(x) = w` for every `x` in `[0, L]`. Then the [end forces](beam-end-forces.md) of `y` are
`K` applied to its [end data](beam-end-data.md) minus the
[consistent load vector](uniform-load-vector.md) of `w`, with the
[beam stiffness matrix](beam-stiffness.md) `K`.
