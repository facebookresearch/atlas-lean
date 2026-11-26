/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GobelNonIntegralityDiagonalIsZigzagBelowGobelResidueWalkOfOdd
import Mathlib.Tactic.NormNum.LegendreSymbol

namespace MathlibExtTest.NumberTheory.GobelNonIntegralityDiagonalIsZigzagBelowGobelResidueWalkOfOdd

open MetaMathlibExt

-- Meeting the diagonal at 2 forces the zigzag switch before 2,
-- so the walk started at 3 equals the diagonal at 4 and 5.
example : gobelResidueWalk 5 3 4 = 4 ∧ gobelResidueWalk 5 3 5 = 5 := by
  have h2 : gobelResidueWalk 5 3 2 = 2 := by norm_num [gobelResidueWalk]
  obtain ⟨m, _, hlt, heq⟩ := diagonal_isZigzagBelow_gobelResidueWalk_of_odd 5 3 (by decide) ⟨2, rfl⟩ ⟨1, rfl⟩ (by decide)
  have hm2 : m < 2 := by
    by_contra hc
    have h2m : 2 ≤ m := not_lt.mp hc
    have h := hlt 2 (by decide) h2m
    change (2 : ℤ) < ((gobelResidueWalk 5 3 2 : ℕ) : ℤ) at h
    rw [h2] at h
    norm_num at h
  have h4 : gobelResidueWalk 5 3 4 = 4 := by
    have h := heq 4 (by omega) (by decide)
    change (4 : ℤ) = ((gobelResidueWalk 5 3 4 : ℕ) : ℤ) at h
    exact_mod_cast h.symm
  have h5 : gobelResidueWalk 5 3 5 = 5 := by
    have h := heq 5 (by omega) le_rfl
    change (5 : ℤ) = ((gobelResidueWalk 5 3 5 : ℕ) : ℤ) at h
    exact_mod_cast h.symm
  exact ⟨h4, h5⟩

end MathlibExtTest.NumberTheory.GobelNonIntegralityDiagonalIsZigzagBelowGobelResidueWalkOfOdd
