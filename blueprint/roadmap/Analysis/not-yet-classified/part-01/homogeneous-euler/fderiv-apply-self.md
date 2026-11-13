# Euler's homogeneous function theorem

A positively homogeneous function of degree one
that is differentiable at `x` satisfies `fderiv ℝ f x x = f x`.

Proof: homogeneity identifies `t ↦ f (t • x)` with `t ↦ t * f x` on a neighbourhood of `t = 1`,
so Mathlib's `HasFDerivAt.apply_self_eq_smul_of_eventuallyEq` applies with `w = id`.

## Sources

- W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9 (chain rule, Theorem 9.15).
