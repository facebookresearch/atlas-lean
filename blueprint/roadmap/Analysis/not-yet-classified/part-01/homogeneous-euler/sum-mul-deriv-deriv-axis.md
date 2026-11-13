# Differentiated Euler identity

**Differentiated Euler identity**, coordinate form: if `f` is positively homogeneous of degree
one and `C^2` at `x`, then for every coordinate `j`,
`∑ i, x i * deriv (fun s => deriv (fun t => f (x + s • Pi.single j 1 + t • Pi.single i 1)) 0) 0`
vanishes. The summand is the iterated axis-slice partial derivative of `f` at `x` in direction
`i` (inner slice, variable `t`) and then in direction `j` (outer slice, variable `s`); each slice
varies exactly one coordinate.

Proof: the iterated axis-slice derivative is `fderiv ℝ (fderiv ℝ f) x (Pi.single j 1)
(Pi.single i 1)` by Mathlib's `DifferentiableAt.lineDeriv_eq_fderiv` (applied near `x` to `f`
and at `x` to `fun y => fderiv ℝ f y (Pi.single i 1)`) and `HasFDerivAt.clm_apply`; by linearity
the sum is `fderiv ℝ (fderiv ℝ f) x (Pi.single j 1) x`, which vanishes by differentiating Euler's
identity. No symmetry of mixed partials is used.

Relation to `MathlibExt.Analysis.Calculus.HigherPartials`: the summand is
`partialDeriv (partialDeriv f i) j x`. The bridge `partialDeriv_partialDeriv_eq_fderiv_fderiv`
there identifies it with `fderiv ℝ (fderiv ℝ f) x (Pi.single j 1) (Pi.single i 1)` but needs
global `ContDiff ℝ 2 f`; the mixed-partial step of this proof is its localization to
`ContDiffAt ℝ 2 f x`, and the global case follows from this lemma via `ContDiff.contDiffAt`.

## Sources

- W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9.
