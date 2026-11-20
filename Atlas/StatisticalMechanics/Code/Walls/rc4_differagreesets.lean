/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































import Code.Inequalities.PerOrbitCardClose
import Code.Walls.rc3_core

open Finset

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]





def rc4_differSet (k : ConfigSpace α × ConfigSpace α) : Finset α :=
  Finset.univ.filter (fun a => k.1 a ≠ k.2 a)



def rc4_agreeSet (k : ConfigSpace α × ConfigSpace α) : Finset α :=
  Finset.univ.filter (fun a => k.1 a = k.2 a)

omit [DecidableEq α] in
@[simp] theorem rc4_mem_differSet (k : ConfigSpace α × ConfigSpace α) (a : α) :
    a ∈ rc4_differSet k ↔ k.1 a ≠ k.2 a := by
  simp only [rc4_differSet, Finset.mem_filter, Finset.mem_univ, true_and]

omit [DecidableEq α] in
@[simp] theorem rc4_mem_agreeSet (k : ConfigSpace α × ConfigSpace α) (a : α) :
    a ∈ rc4_agreeSet k ↔ k.1 a = k.2 a := by
  simp only [rc4_agreeSet, Finset.mem_filter, Finset.mem_univ, true_and]



omit [DecidableEq α] in

theorem rc4_differSet_disjoint_agreeSet (k : ConfigSpace α × ConfigSpace α) :
    Disjoint (rc4_differSet k) (rc4_agreeSet k) := by
  rw [Finset.disjoint_left]
  intro a ha hg
  rw [rc4_mem_differSet] at ha
  rw [rc4_mem_agreeSet] at hg
  exact ha hg


theorem rc4_agreeSet_eq_compl_differSet (k : ConfigSpace α × ConfigSpace α) :
    rc4_agreeSet k = (rc4_differSet k)ᶜ := by
  ext a
  simp only [rc4_mem_agreeSet, Finset.mem_compl, rc4_mem_differSet, not_not]


theorem rc4_differSet_eq_compl_agreeSet (k : ConfigSpace α × ConfigSpace α) :
    rc4_differSet k = (rc4_agreeSet k)ᶜ := by
  rw [rc4_agreeSet_eq_compl_differSet, compl_compl]


theorem rc4_differSet_union_agreeSet (k : ConfigSpace α × ConfigSpace α) :
    rc4_differSet k ∪ rc4_agreeSet k = Finset.univ := by
  rw [rc4_agreeSet_eq_compl_differSet, Finset.union_compl]



theorem rc4_card_differSet_add_card_agreeSet (k : ConfigSpace α × ConfigSpace α) :
    (rc4_differSet k).card + (rc4_agreeSet k).card = Fintype.card α := by
  rw [rc4_agreeSet_eq_compl_differSet, Finset.card_add_card_compl]



omit [DecidableEq α] in




theorem rc4_orbitKey_valid (p : ConfigSpace α × ConfigSpace α) (a : α)
    (ha : a ∈ rc4_differSet (orbitKey p)) :
    (orbitKey p).1 a = true ∧ (orbitKey p).2 a = false := by
  rw [rc4_mem_differSet] at ha
  exact rc3_core_orbitKey_valid p a ha

omit [DecidableEq α] in


theorem rc4_orbitKey_agree_value (k : ConfigSpace α × ConfigSpace α) (a : α)
    (ha : a ∈ rc4_agreeSet k) : k.1 a = k.2 a := by
  rwa [rc4_mem_agreeSet] at ha

omit [DecidableEq α] in




theorem rc4_orbitKey_value (p : ConfigSpace α × ConfigSpace α) (a : α) :
    (a ∈ rc4_differSet (orbitKey p) ∧ (orbitKey p).1 a = true ∧ (orbitKey p).2 a = false)
      ∨ (a ∈ rc4_agreeSet (orbitKey p) ∧ (orbitKey p).1 a = (orbitKey p).2 a) := by
  by_cases hne : (orbitKey p).1 a = (orbitKey p).2 a
  · right
    exact ⟨(rc4_mem_agreeSet _ a).mpr hne, hne⟩
  · left
    refine ⟨(rc4_mem_differSet _ a).mpr hne, rc3_core_orbitKey_valid p a hne⟩



omit [DecidableEq α] in


theorem rc4_keyFlip_eq_compl_on_differ (k : ConfigSpace α × ConfigSpace α)
    (ω : ConfigSpace α) (a : α) (ha : a ∈ rc4_differSet k) :
    poc_keyFlip k ω a = !ω a := by
  rw [rc4_mem_differSet] at ha
  simp only [poc_keyFlip, poc_flip, show (decide (k.1 a ≠ k.2 a)) = true by simp [ha], if_true]

omit [DecidableEq α] in


theorem rc4_keyFlip_eq_self_on_agree (k : ConfigSpace α × ConfigSpace α)
    (ω : ConfigSpace α) (a : α) (ha : a ∈ rc4_agreeSet k) :
    poc_keyFlip k ω a = ω a := by
  rw [rc4_mem_agreeSet] at ha
  have hne : ¬ (k.1 a ≠ k.2 a) := by rw [not_not]; exact ha
  simp only [poc_keyFlip, poc_flip, show (decide (k.1 a ≠ k.2 a)) = false by simp [ha],
    Bool.false_eq_true, if_false]



omit [Fintype α] [DecidableEq α] in



theorem rc4_snd_recovered (p : ConfigSpace α × ConfigSpace α) (k : ConfigSpace α × ConfigSpace α)
    (hk : orbitKey p = k) : p.2 = poc_keyFlip k p.1 :=
  poc_snd_eq p k hk

omit [DecidableEq α] in



theorem rc4_snd_recovered_pointwise (p : ConfigSpace α × ConfigSpace α)
    (k : ConfigSpace α × ConfigSpace α) (hk : orbitKey p = k) (a : α) :
    (a ∈ rc4_differSet k → p.2 a = !p.1 a) ∧ (a ∈ rc4_agreeSet k → p.2 a = p.1 a) := by
  have h := poc_snd_eq p k hk
  constructor
  · intro ha
    rw [h, rc4_keyFlip_eq_compl_on_differ k p.1 a ha]
  · intro ha
    rw [h, rc4_keyFlip_eq_self_on_agree k p.1 a ha]

end StatMech.Walls
