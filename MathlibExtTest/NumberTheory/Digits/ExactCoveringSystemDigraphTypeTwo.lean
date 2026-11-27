/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.ExactCoveringSystemDigraphTypeTwo

/-! # A Type 2 normal form with two loops -/

open MetaMathlibExt

-- The rules 2m - 3 and -2m have distinct loops at 3 and 0. Their normal form must
-- therefore have a nonzero loop, forcing its odd offset to be divisible by 3.
example : ∃ a : ℕ, Odd a ∧ 3 ∣ a ∧
    Nonempty (ecsdAdj ![2, -2] ![-3, 0] ≃r ecsdAdj ![2, -2] ![0, (a : ℤ)]) := by
  obtain ⟨a, ha, ⟨e⟩⟩ := ecsd_type_two_relIso (-3) 0 ⟨-2, rfl⟩
  have loop_zero := e.map_rel_iff.mpr ((ecsdAdj_two 2 (-2) (-3) 0 0 0).mpr (Or.inr rfl))
  have loop_three := e.map_rel_iff.mpr ((ecsdAdj_two 2 (-2) (-3) 0 3 3).mpr (Or.inl rfl))
  rw [ecsdAdj_two] at loop_zero loop_three
  have hne : e 0 ≠ e 3 := e.injective.ne (by decide)
  exact ⟨a, ha, by omega, ⟨e⟩⟩
