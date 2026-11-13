# Differentiated Euler identity

**Differentiated Euler identity**, coordinate-free form: if `f` is positively homogeneous of
degree one and `C^2` at `x`, then the second Fréchet derivative of `f` at `x` vanishes once its
first argument is `x`, i.e. `fderiv ℝ (fderiv ℝ f) x x v = 0` for every `v`. Equivalently, by
Mathlib's `iteratedFDeriv_two_apply`, `iteratedFDeriv ℝ 2 f x ![x, v] = 0` for every `v`.

Proof: differentiate Euler's identity `fderiv ℝ f y y = f y`, valid near `x`, by the product rule
`HasFDerivAt.clm_apply`; this gives `fderiv ℝ (fderiv ℝ f) x v x = 0`, and the symmetry of the
second derivative (`ContDiffAt.isSymmSndFDerivAt`) swaps the two arguments.

## Sources

- W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9 (Theorem 9.41).
