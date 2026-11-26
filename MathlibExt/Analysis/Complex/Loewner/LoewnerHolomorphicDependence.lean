/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.Complex.Loewner.LoewnerMaximal

/-!
# Holomorphy and conformality of the Loewner maps

For a continuous driving function `W` and `t ≥ 0`, the maximal Loewner map
`g_t = loewnerMaximalMaps W t` is complex differentiable with nonzero derivative at every point of
the unswallowed domain `H_t = loewnerUnswallowedDomain W t`, hence holomorphic and conformal there
(`loewnerMaximalMaps_differentiableOn`, `loewnerMaximalMaps_conformalAt`). Together with
`loewnerMaximalMaps_bijOn_upperHalfPlane` this shows that `g_t` is a conformal bijection
`H_t → ℍ`. These results are proved in `LoewnerMaximal` and re-exported here, not redeclared.

The canonical proof first treats short times `u < (Im z)² / 16`, where the flow is given by a local
Picard–Lindelöf chart: the difference quotient of two solutions satisfies a linear ODE, solved
explicitly by `linearODE_terminal_eq_initial_mul_exp_integral`, and dominated convergence gives
`g_u'(z) = exp ∫₀ᵘ -2 / (g_s(z) - W_s)² ds` (`loewnerInitialJacobian`). General times follow by
composing short-time maps of shifted drivers through the flow property.

This file additionally proves `loewnerField_hasDerivAt_initial`, the derivative of the vector
field itself away from the driving point.

## Main definitions (from `LoewnerMaximal`)

* `loewnerInitialVariationalCoefficient`, `loewnerInitialJacobian`: the variational equation and
  its solution `exp ∫ -2/(g_s(z) - W_s)²`.
* `HasLoewnerLocalInitialVariationalFormula W`: the short-time derivative formula for every
  time-shift of `W`; proved for continuous `W` (`hasLoewnerLocalInitialVariationalFormula`).

## Main results

* `loewnerField_hasDerivAt_initial`: the vector-field derivative away from the driving point.
* `loewnerMaximalMaps_hasDerivAt_of_lt_im_sq_div_sixteen` (from `LoewnerMaximal`):
  `g_u'(z) = loewnerInitialJacobian W u z` for short times.
* `exists_loewnerMaximalMaps_hasDerivAt_ne_zero`, `loewnerMaximalMaps_differentiableOn`,
  `loewnerMaximalMaps_conformalAt` (from `LoewnerMaximal`): `g_t` is holomorphic with nonvanishing
  derivative on `H_t`.

## References

* G. F. Lawler, *Conformally Invariant Processes in the Plane*, Mathematical Surveys and Monographs
  114, Amer. Math. Soc., 2005, Chapter 4.
-/

@[expose] public section

open Complex

namespace StatMech.SLE

/-- The derivative of the Loewner vector field `2 / (z - W_t)` in `z` is `-2 / (z - W_t)²`. -/
theorem loewnerField_hasDerivAt_initial
    (W : ℝ → ℝ) (t : ℝ) {z : ℂ}
    (hz : z ≠ (W t : ℂ)) :
    HasDerivAt (loewnerField W t)
      (-2 / (z - (W t : ℂ)) ^ 2) z := by
  have hden : z - (W t : ℂ) ≠ 0 := sub_ne_zero.mpr hz
  rw [show loewnerField W t = fun w => 2 / (w - (W t : ℂ)) from
    funext (loewnerField_apply W t)]
  simpa [hden, Pi.div_def] using
    (hasDerivAt_const z (2 : ℂ)).div
      ((hasDerivAt_id z).sub_const (W t : ℂ)) hden

end StatMech.SLE
