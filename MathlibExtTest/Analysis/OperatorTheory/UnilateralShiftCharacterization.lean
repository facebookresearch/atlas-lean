/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.OperatorTheory.UnilateralShiftCharacterization

open MathlibExt.Analysis.OperatorTheory.UnilateralShiftCharacterizationWanted

-- The old predicate remains transparent, without a completeness assumption.
example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : H →L[ℂ] H) :
    IsShift T ↔ ∃ b : HilbertBasis ℕ ℂ H, ∀ n : ℕ, T (b n) = b (n + 1) := Iff.rfl

-- The identity is isometric, but its iterated ranges all contain the nonzero vector 1.
example : ¬ IsShift (ContinuousLinearMap.id ℂ ℂ) := by
  let T := ContinuousLinearMap.id ℂ ℂ
  intro h
  have hPure := ((isShift_iff_isometry_iInf_range_pow_eq_bot_finrank_orthogonal_eq_one
    (T := T)).mp h).2.1
  have hOne : (1 : ℂ) ∈ ⨅ n : ℕ, LinearMap.range (T.toLinearMap ^ (n + 1)) := by
    refine (Submodule.mem_iInf _).mpr fun n ↦ ⟨1, ?_⟩
    simp [T]
  rw [hPure, Submodule.mem_bot] at hOne
  exact one_ne_zero hOne

#print axioms IsShift
#print axioms isShift_iff_isometry_iInf_range_pow_eq_bot_finrank_orthogonal_eq_one
