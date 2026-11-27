# Lattice correction factor of the exponential tail

For real numbers `θ`, `h` and `t`, the lattice correction factor is `φ(t) = e^{-θ (t⁺ - t)}`, where
`t⁺ = (⌊t / h⌋ + 1) h` is the [lattice point](lattice-above.md) of `t`: the factor with
`e^{-θ t⁺} = φ(t) e^{-θ t}`. For `h ≠ 0` it equals `e^{-θ h (1 - {t / h})}`, where `{t / h}` is the
fractional part of `t / h`, and it is [periodic with period `h`](lattice-corr-add.md); for a
positive span `h > 0` and `θ > 0` it lies in `[e^{-θ h}, 1)`. At `h = 0`, where `t⁺ = 0` by the
convention `x / 0 = 0`, it is `e^{θ t}`, which for `θ ≠ 0` has no nonzero period.
