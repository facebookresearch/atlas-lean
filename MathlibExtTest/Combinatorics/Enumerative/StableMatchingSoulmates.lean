/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.StableMatchingSoulmates

/-! # Tests for stable matching with all but one soulmate pair -/

namespace MetaMathlibExt.StableMatchingSequences.StableMatchingSoulmatesTest

-- Men 0 and 1 have soulmates. Man 2 proposes to women 0, 1 and 2 in that order.
private def profile : PreferenceProfile 3 :=
  (fun i => Equiv.swap 0 (if i = 2 then 0 else i), fun j => Equiv.swap 0 j)

example : galeShapleyRounds profile = 3 := by
  have hcount : soulmatePairCount profile = 3 - 1 := by
    let pairs : Finset (Fin 3 × Fin 3) := {(0, 0), (1, 1)}
    have hpairs : ∀ x : Fin 3 × Fin 3, x ∈ pairs ↔ IsSoulmatePair profile x.1 x.2 := by
      simp only [IsSoulmatePair]
      decide
    let := Fintype.subtype pairs hpairs
    rw [soulmatePairCount, Nat.card_eq_fintype_card, Fintype.card_of_subtype pairs hpairs]
    decide
  have hstable : IsStableMatching profile (Equiv.refl _) := by
    rw [isStableMatching_iff]
    decide
  have hno : ∀ j, ¬ IsSoulmatePair profile 2 j := by
    simp only [IsSoulmatePair]
    decide
  exact (unique_stable_matching_of_soulmatePairCount_eq_pred profile hcount).2 _ hstable 2 hno

-- At n = 0 the predecessor count is zero and there is still a unique stable matching.
example (P : PreferenceProfile 0) : ∃! μ : Equiv.Perm (Fin 0), IsStableMatching P μ := by
  have hcount : soulmatePairCount P = 0 - 1 := by simp [soulmatePairCount]
  exact (unique_stable_matching_of_soulmatePairCount_eq_pred P hcount).1

end MetaMathlibExt.StableMatchingSequences.StableMatchingSoulmatesTest
