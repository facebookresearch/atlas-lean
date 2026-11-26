/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.LinearCombination
import MathlibExt.NumberTheory.Digits.BasePhiRepresentationsBergmanLowestPositionLucasInterval

/-!
# Tests for the lowest Bergman digit from the Lucas interval
-/

open scoped goldenRatio

namespace MathlibExtTest.NumberTheory.Digits.BasePhiRepresentationsBergmanLowestPositionLucasInterval

open MetaMathlibExt

-- The Bergman expansion of `2` is `{1, -2}`; since `2 ∈ [L_1 + 1, L_2 - 1]`, the lowest
-- position is `-2`.
example : (-(-2 : ℤ) = 2 * (0 : ℕ) + 2) := by
  have hR : IsLeast ((({1, -2} : Finset ℤ)) : Set ℤ) (-2) := by
    constructor
    · exact by decide
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
      omega
  have h := (bergman_lowest_position_lucasInterval 2 0 isBergmanExpansion_one_neg_two
    (by rw [basePhiValue_one_neg_two]; norm_num) hR).2 (by decide)
  exact h

-- The Bergman expansion of `3` is `{-2, 2}`; since `3 ∈ [L_2, L_3]`, the lowest position
-- is `-2`.
example : (-(-2 : ℤ) = 2 * (1 : ℕ)) := by
  have h1 : φ⁻¹ = φ - 1 := by
    rw [Real.inv_goldenRatio, ← Real.one_sub_goldenConj]; ring
  have hinv : φ ^ (-2 : ℤ) = 2 - φ := by
    rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, zpow_neg, zpow_ofNat, ← inv_pow, h1]
    linear_combination Real.goldenRatio_sq
  have hval : basePhiValue ({-2, 2} : Finset ℤ) = ((3 : ℕ) : ℝ) := by
    rw [basePhiValue, Finset.sum_insert (by decide), Finset.sum_singleton, zpow_ofNat, hinv]
    linear_combination Real.goldenRatio_sq
  have hS : IsBergmanExpansion ({-2, 2} : Finset ℤ) := by
    unfold IsBergmanExpansion
    decide
  have hR : IsLeast ((({-2, 2} : Finset ℤ)) : Set ℤ) (-2) := by
    constructor
    · exact by decide
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
      omega
  have h := (bergman_lowest_position_lucasInterval 3 1 hS hval hR).1 (by decide)
  exact h

-- Any Bergman expansion of `6 ∈ [L_3 + 1, L_4 - 1]` has lowest position `-4`.
example {S : Finset ℤ} (hS : IsBergmanExpansion S)
    (hSN : basePhiValue S = ((6 : ℕ) : ℝ)) {R : ℤ}
    (hR : IsLeast (S : Set ℤ) R) : R = -4 := by
  have h := (bergman_lowest_position_lucasInterval 6 1 hS hSN hR).2 (by decide)
  omega

end MathlibExtTest.NumberTheory.Digits.BasePhiRepresentationsBergmanLowestPositionLucasInterval
