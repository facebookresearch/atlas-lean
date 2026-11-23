# Periodic lattice correction of the exponential tail

For real numbers `θ`, `h` and `t`, the periodic correction is `φ(t) = e^{-θ (t⁺ - t)}`, where
`t⁺ = (⌊t / h⌋ + 1) h` is the [lattice point above](lattice-above.md) `t`: the factor with
`e^{-θ t⁺} = φ(t) e^{-θ t}`. For `h ≠ 0` it equals `e^{-θ h (1 - {t / h})}`, where `{t / h}` is the
fractional part of `t / h`, and for `θ > 0` and `h > 0` it lies in `[e^{-θ h}, 1)`. At `h = 0`,
where `t⁺ = 0` by the convention `x / 0 = 0`, it is `e^{θ t}`.
