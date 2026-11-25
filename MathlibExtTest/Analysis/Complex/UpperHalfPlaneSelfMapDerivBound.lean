/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.UpperHalfPlaneSelfMapDerivBound
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

open Complex
open UpperHalfPlane (upperHalfPlaneSet)
open MathlibExt.Analysis.Complex.UpperHalfPlaneSelfMapDerivBoundWanted

-- The affine automorphism taking i to w has positive slope equal to the height of w.
example :
    let w := exp ((2 * Real.pi * I) / 3)
    0 < w.im ∧ w.im ≤ Real.sqrt (3 / 2 : ℝ) := by
  let w := exp ((2 * Real.pi * I) / 3)
  have hw : 0 < w.im := by
    simpa [w, exp_im, mul_re, mul_im] using
      Real.sin_pos_of_pos_of_lt_pi (x := 2 * Real.pi / 3) (by positivity)
        (by linarith [Real.pi_pos])
  refine ⟨hw, ?_⟩
  let f (z : ℂ) := (w.re : ℂ) + (w.im : ℂ) * z
  have hf' (z : ℂ) : HasDerivAt f (w.im : ℂ) z := by
    simpa [f] using ((hasDerivAt_id z).const_mul (w.im : ℂ)).const_add (w.re : ℂ)
  have hm : Set.MapsTo f upperHalfPlaneSet upperHalfPlaneSet := fun z hz ↦ by
    simpa [upperHalfPlaneSet, f, mul_im] using mul_pos hw (show 0 < z.im from hz)
  have h := norm_deriv_I_le_sqrt_three_halves_of_mapsTo_upperHalfPlane f
    (fun z _ ↦ (hf' z).differentiableAt.differentiableWithinAt) hm (re_add_im w)
  simpa only [(hf' I).deriv, Complex.norm_of_nonneg hw.le] using h
