/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.ExactCoveringSystemDigraphEcsdTypeOneRelIso

/-! # Tests for the Type 1 normal form -/

namespace MathlibExtTest.NumberTheory.Digits.ExactCoveringSystemDigraphEcsdTypeOneRelIso

open MetaMathlibExt

-- The rules `2m` and `2m + 1` have loops at `0` and `-1`, so the normal-form
-- isomorphism sends them to the two loops `0` and `a` of `G(2n, 2n - a)`.
example : ∃ a : ℕ, ∃ e : ecsdAdj ![2, 2] ![0, 1] ≃r ecsdAdj ![2, 2] ![0, -(a : ℤ)],
    Odd a ∧ ((e 0 = 0 ∧ e (-1) = (a : ℤ)) ∨ (e 0 = (a : ℤ) ∧ e (-1) = 0)) := by
  obtain ⟨a, ha, ⟨e⟩⟩ := ecsd_type_one_relIso 0 1 ⟨-1, rfl⟩
  have loop_zero := e.map_rel_iff.mpr ((ecsdAdj_two 2 2 0 1 0 0).mpr (Or.inl rfl))
  have loop_neg := e.map_rel_iff.mpr ((ecsdAdj_two 2 2 0 1 (-1) (-1)).mpr (Or.inr rfl))
  rw [ecsdAdj_two] at loop_zero loop_neg
  have hne : e 0 ≠ e (-1) := e.injective.ne (by decide)
  exact ⟨a, e, ha, by omega⟩

end MathlibExtTest.NumberTheory.Digits.ExactCoveringSystemDigraphEcsdTypeOneRelIso
