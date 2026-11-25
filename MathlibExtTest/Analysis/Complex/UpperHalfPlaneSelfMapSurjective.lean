/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Calculus.FDeriv.Add
import MathlibExt.Analysis.Complex.UpperHalfPlaneSelfMapSurjective

open MathlibExt.Analysis.Complex.UpperHalfPlaneSelfMapSurjectiveWanted

-- A real translation on the closed upper half-plane may be redefined arbitrarily below it.
example (below : ℂ → ℂ) :
    (fun z : ℂ ↦ if 0 ≤ z.im then z + 1 else below z) '' {z : ℂ | 0 < z.im} =
      {w : ℂ | 0 < w.im} := by
  apply image_upperHalfPlane_eq_of_real_on_real
  · exact (continuous_id.add_const 1).continuousOn.congr fun z hz ↦ ite_eq_left hz
  · intro z hz
    simp [hz]
  · simp
  · exact (differentiable_id.add_const 1).differentiableOn.congr
      fun z hz ↦ ite_eq_left (le_of_lt hz)
  · rintro ⟨c, hc⟩
    have h := (hc Complex.I (by simp)).trans (hc (1 + Complex.I) (by simp)).symm
    simpa using congrArg Complex.re h
