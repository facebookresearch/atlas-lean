/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.MeasureTheory.InfConvolutionLipschitz

/-! # Tests for Lipschitz regularization by inf-convolution -/

open MathlibExt.MeasureTheory.InfConvolutionLipschitzWanted

variable {X : Type*} [MetricSpace X]

-- At slope zero the estimate gives equality at every pair of points.
example (f : X → ENNReal) (hf : LowerSemicontinuous f) (hp : ∃ p, f p < ⊤) (x y : X) :
    (g f 0 x).toReal = (g f 0 y).toReal := by
  simpa only [Nat.cast_zero, zero_mul, abs_nonpos_iff, sub_eq_zero] using
    abs_toReal_g_sub_le_mul_dist f hf hp 0 x y

-- A function zero at one point and infinite elsewhere gives exactly the distance penalty.
example [DecidableEq X] (a x : X) (n : ℕ) :
    g (fun p ↦ if p = a then 0 else ⊤) n x = n * ENNReal.ofReal (dist x a) := by
  simp only [g, sInf_range]
  apply le_antisymm
  · exact (iInf_le _ a).trans (by simp)
  · refine le_iInf fun p ↦ ?_
    by_cases h : p = a <;> simp [h]
