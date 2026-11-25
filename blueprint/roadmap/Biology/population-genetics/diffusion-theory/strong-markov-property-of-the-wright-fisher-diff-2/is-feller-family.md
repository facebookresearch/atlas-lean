# Feller families of kernels on the unit interval

A family `κ = (κ_t)_{t ≥ 0}` of kernels on `[0, 1]`, not assumed finite or Markov, is Feller if, for
every time `t ≥ 0` and every continuous `g : [0, 1] → ℝ`, the function `x ↦ ∫ g(y) κ_t(x, dy)` is
continuous on `[0, 1]`: the kernels map continuous functions to continuous functions. The integral
is a real integral, taken to be `0` when `g` is not integrable against `κ_t(x, ·)` (for instance a
nonzero constant `g` against an infinite measure); for Markov kernels, the usual setting, every
continuous `g` is integrable.
