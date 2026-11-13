/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












































import Code.Foundations.ConfigSpace
import Code.Inequalities.IncreasingEvent

namespace StatMech

namespace BeffaraDC

open ConfigSpace

variable {E : Type*} [Fintype E]








noncomputable def hammingToSet (A : Set (ConfigSpace E)) (ω : ConfigSpace E) : ℕ :=
  sInf (hammingDist ω '' A)



lemma hammingToSet_le (A : Set (ConfigSpace E)) {a : ConfigSpace E} (ha : a ∈ A)
    (ω : ConfigSpace E) : hammingToSet A ω ≤ hammingDist ω a :=
  Nat.sInf_le ⟨a, ha, rfl⟩





lemma exists_realizer (A : Set (ConfigSpace E)) (hne : A.Nonempty) (ω : ConfigSpace E) :
    ∃ a ∈ A, hammingDist ω a = hammingToSet A ω := by
  obtain ⟨a, haA, ha⟩ := Nat.sInf_mem (hne.image (hammingDist ω))
  exact ⟨a, haA, ha⟩


lemma hammingToSet_eq_zero_of_mem (A : Set (ConfigSpace E)) {ω : ConfigSpace E}
    (h : ω ∈ A) : hammingToSet A ω = 0 :=
  Nat.le_zero.mp (Nat.sInf_le ⟨ω, h, hammingDist_self ω⟩)




theorem hammingToSet_eq_zero_iff (A : Set (ConfigSpace E)) (hne : A.Nonempty)
    (ω : ConfigSpace E) : hammingToSet A ω = 0 ↔ ω ∈ A := by
  constructor
  · intro h
    obtain ⟨a, haA, ha⟩ := exists_realizer A hne ω
    rw [h] at ha
    rw [hammingDist_eq_zero.mp ha]
    exact haA
  · exact hammingToSet_eq_zero_of_mem A






theorem hammingToSet_le_add (A : Set (ConfigSpace E)) (hne : A.Nonempty)
    (ω ω' : ConfigSpace E) :
    hammingToSet A ω ≤ hammingDist ω ω' + hammingToSet A ω' := by
  obtain ⟨a, haA, ha⟩ := exists_realizer A hne ω'
  calc hammingToSet A ω
      ≤ hammingDist ω a := hammingToSet_le A haA ω
    _ ≤ hammingDist ω ω' + hammingDist ω' a := hammingDist_triangle ω ω' a
    _ = hammingDist ω ω' + hammingToSet A ω' := by rw [ha]














theorem hammingToSet_antitone (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    {ω ω' : ConfigSpace E} (hle : ω ≤ ω') :
    hammingToSet A ω' ≤ hammingToSet A ω := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp [hammingToSet]
  · obtain ⟨a, haA, ha⟩ := exists_realizer A hne ω
    
    set a' : ConfigSpace E := fun e => a e || ω' e with ha'
    have ha'A : a' ∈ A := hA (fun e => le_sup_left) haA
    
    have hbound : hammingDist ω' a' ≤ hammingDist ω a := by
      apply Finset.card_le_card
      intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ha'] at he ⊢
      have hpt : ω e ≤ ω' e := hle e
      rcases hbo : ω' e with _ | _
      · 
        simp only [hbo, Bool.or_false] at he
        have hae : a e = true := by
          cases h : a e with
          | false => simp [h] at he
          | true => rfl
        have hwe : ω e = false := by
          rw [hbo] at hpt
          cases h : ω e with
          | false => rfl
          | true => rw [h] at hpt; exact absurd hpt (by decide)
        rw [hwe, hae]; decide
      · 
        simp [hbo] at he
    calc hammingToSet A ω'
        ≤ hammingDist ω' a' := hammingToSet_le A ha'A ω'
      _ ≤ hammingDist ω a := hbound
      _ = hammingToSet A ω := ha

end BeffaraDC

end StatMech
