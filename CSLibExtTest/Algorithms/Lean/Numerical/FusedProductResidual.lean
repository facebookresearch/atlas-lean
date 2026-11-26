/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Numerical.FusedProductResidual
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Rat.Floor

/-! # Fixtures for the error-free product residual -/

namespace Cslib.Algorithms.Lean.FloatingPoint

-- At the lower exponent bound, `7 * 7` rounds to `48` and leaves the subnormal `1`.
example : IsFloatIn 3 0 3 (1 : ℚ) ∧ fl 3 (1 : ℚ) = 1 ∧ 48 + fl 3 (1 : ℚ) = 49 := by
  have ha : IsFloatIn 3 0 3 (7 : ℚ) := ⟨7, 0, by decide, le_rfl, by decide, by norm_num⟩
  have hπ : fl 3 (7 * 7 : ℚ) = 48 := by decide +kernel
  have hfπ : IsFloatIn 3 0 3 (fl 3 (7 * 7 : ℚ)) := by
    rw [hπ]
    exact ⟨6, 3, by decide, by decide, le_rfl, by norm_num⟩
  have h := fusedProductResidual (by decide) (by decide) (by decide) ha ha (by decide +kernel) hfπ
  simp only [hπ] at h
  norm_num at h
  exact h

-- The result also applies when the exact product's magnitude exceeds the finite maximum `120`.
example : IsFloatIn 4 0 3 (-1 : ℚ) ∧ fl 4 (-1 : ℚ) = -1 ∧ -120 + fl 4 (-1 : ℚ) = -121 := by
  have ha : IsFloatIn 4 0 3 (-11 : ℚ) := ⟨-11, 0, by decide, le_rfl, by decide, by norm_num⟩
  have hb : IsFloatIn 4 0 3 (11 : ℚ) := ⟨11, 0, by decide, le_rfl, by decide, by norm_num⟩
  have hπ : fl 4 (-11 * 11 : ℚ) = -120 := by decide +kernel
  have hfπ : IsFloatIn 4 0 3 (fl 4 (-11 * 11 : ℚ)) := by
    rw [hπ]
    exact ⟨-15, 3, by decide, by decide, le_rfl, by norm_num⟩
  have h := fusedProductResidual (by decide) (by decide) (by decide) ha hb (by decide +kernel) hfπ
  simp only [hπ] at h
  norm_num at h
  exact h

-- An exactly representable product leaves zero, which is also in the bounded format.
example : IsFloatIn 3 0 3 (0 : ℚ) ∧ fl 3 (0 : ℚ) = 0 ∧ 16 + fl 3 (0 : ℚ) = 16 := by
  have ha : IsFloatIn 3 0 3 (4 : ℚ) := ⟨4, 0, by decide, le_rfl, by decide, by norm_num⟩
  have hπ : fl 3 (4 * 4 : ℚ) = 16 := by decide +kernel
  have hfπ : IsFloatIn 3 0 3 (fl 3 (4 * 4 : ℚ)) := by
    rw [hπ]
    exact ⟨4, 2, by decide, by decide, by decide, by norm_num⟩
  have h := fusedProductResidual (by decide) (by decide) (by decide) ha ha (by decide +kernel) hfπ
  simp only [hπ] at h
  norm_num at h ⊢
  exact h

end Cslib.Algorithms.Lean.FloatingPoint
