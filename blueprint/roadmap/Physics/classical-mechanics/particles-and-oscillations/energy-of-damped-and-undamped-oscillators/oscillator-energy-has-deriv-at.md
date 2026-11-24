# Oscillator energy has Deriv At

Energy of an undamped oscillator: `E t = (deriv x t) ^ 2 / 2 + ω₀ ^ 2 * (x t) ^ 2 / 2`.
If `x` satisfies `x'' = -ω₀ ^ 2 * x` (as `HasDerivAt` data at `t`), then
`E` has derivative `0` at `t`.
