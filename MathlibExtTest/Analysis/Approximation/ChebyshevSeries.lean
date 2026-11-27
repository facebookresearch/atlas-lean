/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Approximation.ChebyshevSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace MathlibExtTest.Analysis.Approximation.ChebyshevSeries

open MathlibExt.Analysis.Approximation.ChebyshevInterpolationWanted
open Polynomial Real

/-- The coefficient in degree zero preserves complex constants. -/
example (c : ℂ) : chebCoeff (fun _ => c) 0 = c := by
  simp [chebCoeff, intervalIntegral.integral_const, Complex.real_smul]

/-- The normalization in positive degree gives the identity function coefficient one. -/
example : chebCoeff (fun x => (x : ℂ)) 1 = 1 := by
  simp only [chebCoeff, one_ne_zero, ite_false, Nat.cast_one, one_mul]
  simp_rw [← Complex.ofReal_mul, ← pow_two]
  rw [intervalIntegral.integral_ofReal, integral_cos_sq]
  simp

/-- The pointwise sum includes the left endpoint for a function with a corner at zero. -/
example :
    HasSum (fun k => chebCoeff (fun x => (↑|x| : ℂ)) k *
      (((Chebyshev.T ℝ k).eval (-1) : ℝ) : ℂ)) (1 : ℂ) := by
  have hf : LipschitzOnWith 1 (fun x : ℝ => (↑|x| : ℂ)) (Set.Icc (-1) 1) := by
    intro x _ y _
    rw [Complex.isometry_ofReal.edist_eq, ENNReal.coe_one, one_mul]
    simpa only [edist_dist, Real.dist_eq] using
      ENNReal.ofReal_le_ofReal (abs_abs_sub_abs_le_abs_sub x y)
  simpa using (hasSum_chebCoeff_of_lipschitz hf).2 (-1) (by constructor <;> norm_num)

end MathlibExtTest.Analysis.Approximation.ChebyshevSeries
