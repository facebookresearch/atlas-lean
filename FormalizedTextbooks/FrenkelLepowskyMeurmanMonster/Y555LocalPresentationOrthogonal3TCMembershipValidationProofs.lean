/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact consequences of complete finite source matrix fingerprint certificates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCMembershipCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationFiniteCodes

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Unpack the exact finite matrix and sorted-label check at its actual bounded source index. -/
theorem y322Orthogonal3TCMembershipCheck_unpack (i : Fin 3159)
    (h : y322Orthogonal3TCMembershipCheckAt i.val) :
    y322Orthogonal3TCMembershipEval
        (y322Orthogonal3TCCacheMatrix (y322Orthogonal3TCRepresentativeCache i)) =
      y322Orthogonal3TCMembershipValue i ∧
    y322Orthogonal3TCMembershipValue i =
      y322Orthogonal3TCMembershipSorted (y322Orthogonal3TCMembershipSortPosition i) ∧
    y322Orthogonal3TCMembershipInverseSortPosition (y322Orthogonal3TCMembershipSortPosition i) = i ∧
    (if hn : i.val + 1 < 3159 then
      y322Orthogonal3TCMembershipSorted i <
        y322Orthogonal3TCMembershipSorted ⟨i.val + 1, hn⟩
    else True) := by
  simpa only [y322Orthogonal3TCMembershipCheckAt, dite_eq_left i.isLt] using h

/-- Complete exact certificates make the declared fingerprint codes strictly increasing in order. -/
theorem y322Orthogonal3TCMembershipSorted_mono_of_checked
    (h : ∀ i : Fin 3159, y322Orthogonal3TCMembershipCheckAt i.val) :
    StrictMono y322Orthogonal3TCMembershipSorted := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have hc := (y322Orthogonal3TCMembershipCheck_unpack i.castSucc (h i.castSucc)).2.2.2
  have hn : i.castSucc.val + 1 < 3159 := by
    change i.val + 1 < 3159
    have hi := i.isLt
    omega
  rw [dite_eq_left hn] at hc
  exact hc

/-- The declared inverse sorting positions distinguish all exact finite source fingerprints. -/
theorem y322Orthogonal3TCMembershipValue_injective_of_checked
    (h : ∀ i : Fin 3159, y322Orthogonal3TCMembershipCheckAt i.val) :
    Function.Injective y322Orthogonal3TCMembershipValue := by
  have hs := y322SortedFiniteCode_injective y322Orthogonal3TCMembershipSorted
    y322Orthogonal3TCMembershipSortPosition y322Orthogonal3TCMembershipInverseSortPosition
    (y322Orthogonal3TCMembershipSorted_mono_of_checked h)
    (fun i => (y322Orthogonal3TCMembershipCheck_unpack i (h i)).2.2.1)
  intro i j hij
  apply hs
  exact (y322Orthogonal3TCMembershipCheck_unpack i (h i)).2.1.symm.trans
    (hij.trans (y322Orthogonal3TCMembershipCheck_unpack j (h j)).2.1)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
