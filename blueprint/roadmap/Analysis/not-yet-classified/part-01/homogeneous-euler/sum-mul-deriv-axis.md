# Euler's homogeneous function theorem

**Euler's homogeneous function theorem**, coordinate form: the coordinates of `x` weighted by
the axis-slice partial derivatives of `f` at `x` sum to `f x`. The `i`-th axis-slice partial
derivative `deriv (fun t => f (x + t • Pi.single i 1)) 0` varies only the `i`-th coordinate.

Proof: each axis-slice derivative is `partialDeriv f i x` (`partialDeriv_spec`), which is
`fderiv ℝ f x (Pi.single i 1)` by `partialDeriv_eq_fderiv_apply` from
`MathlibExt.Analysis.Calculus.HigherPartials`; linearity and `pi_eq_sum_univ'` reduce the sum to
`fderiv ℝ f x x`, and `IsHomogeneousDegreeOne.fderiv_apply_self` concludes.

## Sources

- W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9.
