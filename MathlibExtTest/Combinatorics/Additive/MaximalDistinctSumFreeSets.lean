/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.MaximalDistinctSumFreeSets
import Mathlib.Data.ZMod.Basic

namespace MetaMathlibExt.two_rpow_le_maxDistinctSumFreeCount_of_typeOne

-- At the smallest admissible prime, {2, 3} realizes the maximum.
private theorem largest_five : largestSumFreeCard (Set.univ : Set (ZMod 5)) = 2 := by
  let sizes := {k | ∃ T : Finset (ZMod 5), (T : Set (ZMod 5)) ⊆ Set.univ ∧
    IsSumFreeSet (T : Set (ZMod 5)) ∧ T.card = k}
  change sSup sizes = 2
  have upper : ∀ T : Finset (ZMod 5), (∀ x ∈ T, ∀ y ∈ T, x + y ∉ T) → T.card ≤ 2 := by
    decide
  have hu : 2 ∈ upperBounds sizes := by
    rintro k ⟨T, -, hT, rfl⟩
    exact upper T hT
  refine le_antisymm (csSup_le' hu) (le_csSup ⟨2, hu⟩ ?_)
  refine ⟨{2, 3}, Set.subset_univ _, ?_, by decide⟩
  change ∀ x ∈ ({2, 3} : Finset (ZMod 5)), ∀ y ∈ ({2, 3} : Finset (ZMod 5)), x + y ∉ _
  decide

example : 2 ≤ maxDistinctSumFreeCount (ZMod 5) := by
  have htype : IsTypeOneGroup (ZMod 5) 5 := by
    refine ⟨by decide, rfl, by simp, fun q hq _ hd ↦ ?_⟩
    rw [ZMod.card] at hd
    exact (Nat.prime_dvd_prime_iff_eq hq (by decide)).mp hd |>.ge
  have h := two_rpow_le_maxDistinctSumFreeCount_of_typeOne (by decide : 5 ≤ 5) htype
  rw [largest_five] at h
  norm_num at h
  exact_mod_cast h

-- The prime 5 also divides 10, but the smaller prime 2 determines its type.
example : ¬ IsTypeOneGroup (ZMod 10) 5 := by
  intro h
  exact (by decide : ¬5 ≤ 2) (h.2.2.2 2 Nat.prime_two rfl (by simp))

end MetaMathlibExt.two_rpow_le_maxDistinctSumFreeCount_of_typeOne
