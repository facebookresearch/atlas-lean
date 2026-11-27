/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.PermutipleStringsExistsIsPermutipleStringOfHasEulerianCircuitFromZero

namespace MathlibExtTest.NumberTheory.Digits.PermutipleStringsExistsIsPermutipleStringOfHasEulerianCircuitFromZero

open MetaMathlibExt

-- The mother-graph cycles [2, 8], [1, 7] and [9] admit an Eulerian circuit
-- through zero, hence yield a permutiple string of length five.
example : ∃ s : List (ℕ × ℕ), s.length = 5 ∧ IsPermutipleString 4 10 s := by
  have hcs : ∀ vs ∈ ({[2, 8], [1, 7], [9]} : Multiset (List ℕ)), IsMotherGraphCycle 4 10 vs := by
    intro vs hvs
    simp at hvs
    rcases hvs with rfl | rfl | rfl
    · unfold IsMotherGraphCycle
      decide
    · unfold IsMotherGraphCycle
      decide
    · unfold IsMotherGraphCycle
      decide
  have heuler : HasEulerianCircuitFromZero
      (multiImageUnion 4 10 ({[2, 8], [1, 7], [9]} : Multiset (List ℕ))) := by
    refine ⟨[(0, 3), (3, 3), (3, 3), (3, 0), (0, 0)], by decide, by decide, by decide, by decide, by decide⟩
  obtain ⟨s, hs_eq, hs_str⟩ :=
    exists_isPermutipleString_of_hasEulerianCircuitFromZero 4 10 (by decide) (by decide) _ hcs heuler
  refine ⟨s, ?_, hs_str⟩
  have hcard : (s : Multiset (ℕ × ℕ)).card = 5 := by
    rw [hs_eq]
    decide
  rw [Multiset.coe_card s] at hcard
  exact hcard

end MathlibExtTest.NumberTheory.Digits.PermutipleStringsExistsIsPermutipleStringOfHasEulerianCircuitFromZero
