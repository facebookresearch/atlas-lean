/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































import Code.Walls.rc28cylrec

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]











noncomputable def rc29_flipA (a : α) (ℬ : Finset (Finset α)) : Finset (Finset α) :=
  ℬ.image (fun S => if a ∈ S then S.erase a else insert a S)

omit [Fintype α] in

theorem rc29_toggle_involutive (a : α) (S : Finset α) :
    (if a ∈ (if a ∈ S then S.erase a else insert a S) then
        (if a ∈ S then S.erase a else insert a S).erase a
      else insert a (if a ∈ S then S.erase a else insert a S)) = S := by
  by_cases ha : a ∈ S
  · simp only [ha, if_true]
    have : a ∉ S.erase a := Finset.notMem_erase a S
    simp only [this, if_false, Finset.insert_erase ha]
  · simp only [ha, if_false]
    have : a ∈ insert a S := Finset.mem_insert_self a S
    simp only [this, if_true, Finset.erase_insert ha]

omit [Fintype α] in


theorem rc29_mem_flipA (a : α) (ℬ : Finset (Finset α)) (S : Finset α) :
    S ∈ rc29_flipA a ℬ ↔ (if a ∈ S then S.erase a else insert a S) ∈ ℬ := by
  rw [rc29_flipA, Finset.mem_image]
  constructor
  · rintro ⟨T, hT, rfl⟩
    rwa [rc29_toggle_involutive a T]
  · intro h
    exact ⟨_, h, rc29_toggle_involutive a S⟩

omit [Fintype α] in




theorem rc29_flipA_nonMemberSubfamily (a : α) (ℬ : Finset (Finset α)) :
    (rc29_flipA a ℬ).nonMemberSubfamily a = ℬ.memberSubfamily a := by
  ext S
  rw [Finset.mem_nonMemberSubfamily, rc29_mem_flipA, Finset.mem_memberSubfamily]
  constructor
  · rintro ⟨hmem, haS⟩
    rw [if_neg haS] at hmem
    exact ⟨hmem, haS⟩
  · rintro ⟨hmem, haS⟩
    rw [if_neg haS]
    exact ⟨hmem, haS⟩

omit [Fintype α] in




theorem rc29_flipA_memberSubfamily (a : α) (ℬ : Finset (Finset α)) :
    (rc29_flipA a ℬ).memberSubfamily a = ℬ.nonMemberSubfamily a := by
  ext S
  rw [Finset.mem_memberSubfamily, rc29_mem_flipA, Finset.mem_nonMemberSubfamily]
  constructor
  · rintro ⟨hmem, haS⟩
    have hain : a ∈ insert a S := Finset.mem_insert_self a S
    rw [if_pos hain, Finset.erase_insert haS] at hmem
    exact ⟨hmem, haS⟩
  · rintro ⟨hmem, haS⟩
    have hain : a ∈ insert a S := Finset.mem_insert_self a S
    rw [if_pos hain, Finset.erase_insert haS]
    exact ⟨hmem, haS⟩











open Classical in









theorem rc29_flippedBox_crossRecursion {E : Finset α} (𝒜 ℬ : Finset (Finset α)) {a : α}
    (haE : a ∈ E) :
    #(rc28_famCylBoxE E 𝒜 (rc29_flipA a ℬ))
      ≤ #(rc28_famCylBoxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a))
        + #(rc28_famCylBoxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a)) := by
  have h := rc28_sameSideRecursion 𝒜 (rc29_flipA a ℬ) haE
  rwa [rc29_flipA_nonMemberSubfamily, rc29_flipA_memberSubfamily] at h












open Classical in






theorem rc29_flippedReflE_sameSideRecursion {E : Finset α} (𝒜 ℬ : Finset (Finset α)) {a : α}
    (haE : a ∈ E) :
    #(rc14_reflE E 𝒜 (rc29_flipA a ℬ))
      = #(rc14_reflE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a))
        + #(rc14_reflE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a)) := by
  have h := rc27_reflInterRecursion E 𝒜 (rc29_flipA a ℬ) a haE
  rwa [rc29_flipA_memberSubfamily, rc29_flipA_nonMemberSubfamily] at h






















open Classical in





theorem rc29_box_le_flippedReflE {E : Finset α} (𝒜 ℬ : Finset (Finset α)) {a : α} (haE : a ∈ E)
    (hwnn : #(rc28_famCylBoxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a))
        ≤ #(rc14_reflE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a)))
    (hwmm : #(rc28_famCylBoxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a))
        ≤ #(rc14_reflE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a))) :
    #(rc28_famCylBoxE E 𝒜 ℬ) ≤ #(rc14_reflE E 𝒜 (rc29_flipA a ℬ)) := by
  have hrec := rc28_sameSideRecursion 𝒜 ℬ haE
  have hflip := rc29_flippedReflE_sameSideRecursion 𝒜 ℬ haE
  omega











open Classical in





theorem rc29_flipCandidate_of_wall
    (hwall : ∀ (E : Finset α) (𝒜 ℬ : Finset (Finset α)),
      #(rc28_famCylBoxE E 𝒜 ℬ) ≤ #(rc14_reflE E 𝒜 ℬ))
    {E : Finset α} (𝒜 ℬ : Finset (Finset α)) {a : α} (haE : a ∈ E) :
    #(rc28_famCylBoxE E 𝒜 ℬ) ≤ #(rc14_reflE E 𝒜 (rc29_flipA a ℬ)) :=
  rc29_box_le_flippedReflE 𝒜 ℬ haE
    (hwall (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a))
    (hwall (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a))















def rc29_flipAComp (n : ℕ) (a : Fin n) (ℬ : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  ℬ.image (fun S => if a ∈ S then S.erase a else insert a S)

theorem rc29_flipAComp_eq (n : ℕ) (a : Fin n) (ℬ : Finset (Finset (Fin n))) :
    rc29_flipAComp n a ℬ = rc29_flipA a ℬ := rfl



set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in






theorem rc29_box_flip_strictDecrease :
    #(rc28_famCylBoxE (univ : Finset (Fin 3)) ({∅, {0}, {1}})
        ({∅, {0}, {0, 1}, {2}, {0, 2}, {0, 1, 2}}))
      > #(rc28_famCylBoxE (univ : Finset (Fin 3)) ({∅, {0}, {1}})
          (rc29_flipA 0 ({∅, {0}, {0, 1}, {2}, {0, 2}, {0, 1, 2}} : Finset (Finset (Fin 3))))) := by
  rw [← rc29_flipAComp_eq, ← rc28_famCylBoxEComp_eq, ← rc28_famCylBoxEComp_eq]
  decide














set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in





theorem rc29_flipCandidate_witness :
    #(rc28_famCylBoxE (univ : Finset (Fin 3)) ({∅, {0}, {1}, {2}, {0, 1}})
        ({∅, {0}, {1}, {0, 1}, {0, 2}}))
      ≤ #(rc14_reflE (univ : Finset (Fin 3)) ({∅, {0}, {1}, {2}, {0, 1}})
          (rc29_flipA 0 ({∅, {0}, {1}, {0, 1}, {0, 2}} : Finset (Finset (Fin 3))))) := by
  rw [← rc29_flipAComp_eq, ← rc28_famCylBoxEComp_eq, ← rc28_reflEComp_eq]
  decide









open Classical in




theorem rc29_famCylBox_le_reflInter_flip
    (hwall : ∀ (E : Finset α) (𝒜 ℬ : Finset (Finset α)),
      #(rc28_famCylBoxE E 𝒜 ℬ) ≤ #(rc14_reflE E 𝒜 ℬ))
    (𝒜 ℬ : Finset (Finset α)) (a : α) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 (rc29_flipA a ℬ)) := by
  have h := rc29_flipCandidate_of_wall hwall (E := (univ : Finset α)) 𝒜 ℬ (Finset.mem_univ a)
  rwa [rc28_famCylBoxE_univ, rc15_reflE_univ] at h













theorem rc29_toggle_compl (a : α) (S : Finset α) :
    (if a ∈ S then S.erase a else insert a S)ᶜ
      = (if a ∈ Sᶜ then Sᶜ.erase a else insert a Sᶜ) := by
  by_cases ha : a ∈ S
  · have hac : a ∉ Sᶜ := by rw [Finset.mem_compl]; exact fun h => h ha
    rw [if_pos ha, if_neg hac, Finset.compl_erase]
  · have hac : a ∈ Sᶜ := by rw [Finset.mem_compl]; exact ha
    rw [if_neg ha, if_pos hac, Finset.compl_insert]

open Classical in






theorem rc29_reflInter_doubleFlip (a : α) (𝒜 ℬ : Finset (Finset α)) :
    #(rc10_reflInter (rc29_flipA a 𝒜) (rc29_flipA a ℬ)) = #(rc10_reflInter 𝒜 ℬ) := by
  apply Finset.card_bij (fun S _ => (if a ∈ S then S.erase a else insert a S))
  · intro S hS
    rw [rc20_mem_reflInter, rc29_mem_flipA, rc29_mem_flipA] at hS
    rw [rc20_mem_reflInter, rc29_toggle_compl]
    exact hS
  · intro S hS S' hS' h
    have := congrArg (fun T => if a ∈ T then T.erase a else insert a T) h
    simpa only [rc29_toggle_involutive] using this
  · intro T hT
    refine ⟨if a ∈ T then T.erase a else insert a T, ?_, rc29_toggle_involutive a T⟩
    rw [rc20_mem_reflInter] at hT
    rw [rc20_mem_reflInter, rc29_mem_flipA, rc29_mem_flipA, rc29_toggle_involutive,
      rc29_toggle_compl, rc29_toggle_involutive]
    exact hT

end StatMech.Walls
