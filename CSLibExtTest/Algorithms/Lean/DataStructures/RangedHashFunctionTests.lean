/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.DataStructures.RangedHashFunction

/-!
# Tests for ranged hash functions

The two items use opposite priorities on buckets `0` and `2`. The examples distinguish
moving to a new bucket from switching between old buckets, and compare the rank rule with
a legal selection that does make the latter switch.
-/

namespace Cslib.Algorithms.Lean.RangedHashFunctionTests

open RangedHashFunction

-- Even for an infinite bucket universe, a singleton has only one legal choice.
example (f : RangedHashFunction Unit ℕ) (b : ℕ) :
    (f {b} (Set.singleton_nonempty b) ()).val = b :=
  (f {b} (Set.singleton_nonempty b) ()).property

private def ranks : Bool → Fin 3 ≃ Fin 3
  | false => Equiv.refl _
  | true => Equiv.swap 0 2

private def endpoints : Set (Fin 3) := {0, 2}
private theorem endpoints_ne : endpoints.Nonempty := ⟨0, by simp [endpoints]⟩

private def upper : Set (Fin 3) := {1, 2}
private theorem upper_ne : upper.Nonempty := ⟨1, by simp [upper]⟩

private theorem all_first : (ofRanks ranks Set.univ Set.univ_nonempty false).val = 0 :=
  (ofRanks_eq_iff ranks _ _ _).2 ⟨Set.mem_univ _, fun _ _ => Fin.zero_le _⟩

-- The new bucket 0 outranks both old buckets. The second item already preferred 2.
example : (ofRanks ranks upper upper_ne false).val = 1 ∧
    (ofRanks ranks Set.univ Set.univ_nonempty false).val = 0 ∧
    (ofRanks ranks Set.univ Set.univ_nonempty true).val = 2 := by
  refine ⟨(ofRanks_eq_iff ranks _ _ _).2 ⟨by simp [upper], ?_⟩, all_first,
    (ofRanks_eq_iff ranks _ _ _).2 ⟨Set.mem_univ _, ?_⟩⟩
  · intro c hc
    rcases (show c = 1 ∨ c = 2 from hc) with rfl | rfl <;> decide
  · intro c _
    simp only [ranks, Equiv.swap_apply_right]
    exact Fin.zero_le _

-- Adding bucket 1 leaves the larger view's winner 0 available in the old view.
example : (ofRanks ranks endpoints endpoints_ne false).val = 0 := by
  have hmem : (ofRanks ranks Set.univ Set.univ_nonempty false).val ∈ endpoints := by
    rw [all_first]
    simp [endpoints]
  exact (isMonotone_ofRanks ranks endpoints_ne Set.univ_nonempty
    (Set.subset_univ _) false hmem).trans all_first

private noncomputable def family (s : Bool) : RangedHashFunction Unit (Fin 3) :=
  ofRanks (fun _ => ranks s)

-- 0 and 2 can each win for a different seed, but switching from 0 to 2 is impossible
-- under a single draw, whatever the probabilities of the two seeds.
example (μ : PMF Bool) : ((0, 2) : Fin 3 × Fin 3) ∉
    ((μ.map family).map fun f =>
      ((f endpoints endpoints_ne ()).val, (f Set.univ Set.univ_nonempty ()).val)).support := by
  intro hp
  have h := mem_diff_of_joint_move family μ (fun s _ => isMonotone_ofRanks (fun _ => ranks s))
    endpoints_ne Set.univ_nonempty (Set.subset_univ _) () hp (by decide)
  exact h.2 (by simp [endpoints])

-- Prefer 2 if 1 and 2 are both visible, otherwise prefer 0; use any member as fallback.
private noncomputable def switchesOld : RangedHashFunction Unit (Fin 3) := by
  classical
  exact fun V hV _ => if h : 1 ∈ V ∧ 2 ∈ V then ⟨2, h.2⟩
    else if h : 0 ∈ V then ⟨0, h⟩ else ⟨hV.choose, hV.choose_spec⟩

example : ¬ switchesOld.IsMonotone := by
  intro h
  have small : (switchesOld endpoints endpoints_ne ()).val = 0 := by
    simp [switchesOld, endpoints]
  have large : (switchesOld Set.univ Set.univ_nonempty ()).val = 2 := by simp [switchesOld]
  have hmem : (switchesOld Set.univ Set.univ_nonempty ()).val ∈ endpoints := by
    rw [large]
    simp [endpoints]
  have heq := h endpoints_ne Set.univ_nonempty (Set.subset_univ _) () hmem
  rw [small, large] at heq
  exact (by decide : (0 : Fin 3) ≠ 2) heq

end Cslib.Algorithms.Lean.RangedHashFunctionTests
