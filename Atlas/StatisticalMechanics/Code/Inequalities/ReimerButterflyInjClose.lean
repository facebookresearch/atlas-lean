/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Code.Inequalities.ReimerDoubleCoverClose

open Finset
open scoped FinsetFamily

namespace StatMech

open ConfigSpace







def rbi_cfg (a b : Bool) : ConfigSpace (Fin 2) := ![a, b]

@[simp] lemma rbi_cfg_zero (a b : Bool) : rbi_cfg a b 0 = a := rfl
@[simp] lemma rbi_cfg_one (a b : Bool) : rbi_cfg a b 1 = b := rfl


def rbi_A : Set (ConfigSpace (Fin 2)) := {ω | ¬ (ω 0 = true ∧ ω 1 = true)}


def rbi_B : Set (ConfigSpace (Fin 2)) := {ω | ¬ (ω 0 = true ∧ ω 1 = false)}


lemma rbi_fin2_cases (e : Fin 2) : e = 0 ∨ e = 1 := by omega




lemma rbi_FF_in_box :
    rbi_cfg false false ∈ disjointOccurrence rbi_A rbi_B := by
  refine ⟨{a : Fin 2 | a = 1}, {a : Fin 2 | a = 0}, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]; intro a ha hb
    simp only [Set.mem_setOf_eq] at ha hb; omega
  · intro ω' hag
    have h1 : ω' 1 = false := by have := hag 1 (by simp); simpa [rbi_cfg] using this
    simp only [rbi_A, Set.mem_setOf_eq]; rw [h1]; simp
  · intro ω' hag
    have h0 : ω' 0 = false := by have := hag 0 (by simp); simpa [rbi_cfg] using this
    simp only [rbi_B, Set.mem_setOf_eq]; rw [h0]; simp


lemma rbi_FT_in_box :
    rbi_cfg false true ∈ disjointOccurrence rbi_A rbi_B := by
  refine ⟨{a : Fin 2 | a = 0}, {a : Fin 2 | a = 1}, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]; intro a ha hb
    simp only [Set.mem_setOf_eq] at ha hb; omega
  · intro ω' hag
    have h0 : ω' 0 = false := by have := hag 0 (by simp); simpa [rbi_cfg] using this
    simp only [rbi_A, Set.mem_setOf_eq]; rw [h0]; simp
  · intro ω' hag
    have h1 : ω' 1 = true := by have := hag 1 (by simp); simpa [rbi_cfg] using this
    simp only [rbi_B, Set.mem_setOf_eq]; rw [h1]; simp













lemma rbi_force_FF (K : Fin 2 → Bool)
    (hA : OccursOn rbi_A {a : Fin 2 | K a = true} (rbi_cfg false false))
    (hB : OccursOn rbi_B {a : Fin 2 | K a = false} (rbi_cfg false false)) :
    K 0 = false ∧ K 1 = true := by
  have hK0 : K 0 = false := by
    by_contra h; simp only [Bool.not_eq_false] at h
    have hag : agreeOn {a : Fin 2 | K a = false} (rbi_cfg false false) (rbi_cfg true false) := by
      intro e he; simp only [Set.mem_setOf_eq] at he
      rcases rbi_fin2_cases e with rfl | rfl
      · rw [h] at he; exact absurd he (by simp)
      · simp [rbi_cfg]
    have : rbi_cfg true false ∈ rbi_B := hB _ hag
    simp [rbi_B, rbi_cfg] at this
  have hK1 : K 1 = true := by
    by_contra h; simp only [Bool.not_eq_true] at h
    have hag : agreeOn {a : Fin 2 | K a = true} (rbi_cfg false false) (rbi_cfg true true) := by
      intro e he; simp only [Set.mem_setOf_eq] at he
      rcases rbi_fin2_cases e with rfl | rfl
      · rw [hK0] at he; exact absurd he (by simp)
      · rw [h] at he; exact absurd he (by simp)
    have : rbi_cfg true true ∈ rbi_A := hA _ hag
    simp [rbi_A, rbi_cfg] at this
  exact ⟨hK0, hK1⟩








lemma rbi_force_FT (K : Fin 2 → Bool)
    (hA : OccursOn rbi_A {a : Fin 2 | K a = true} (rbi_cfg false true))
    (hB : OccursOn rbi_B {a : Fin 2 | K a = false} (rbi_cfg false true)) :
    K 0 = true ∧ K 1 = false := by
  have hK0 : K 0 = true := by
    by_contra h; simp only [Bool.not_eq_true] at h
    have hag : agreeOn {a : Fin 2 | K a = true} (rbi_cfg false true) (rbi_cfg true true) := by
      intro e he; simp only [Set.mem_setOf_eq] at he
      rcases rbi_fin2_cases e with rfl | rfl
      · rw [h] at he; exact absurd he (by simp)
      · simp [rbi_cfg]
    have : rbi_cfg true true ∈ rbi_A := hA _ hag
    simp [rbi_A, rbi_cfg] at this
  have hK1 : K 1 = false := by
    by_contra h; simp only [Bool.not_eq_false] at h
    have hag : agreeOn {a : Fin 2 | K a = false} (rbi_cfg false true) (rbi_cfg true false) := by
      intro e he; simp only [Set.mem_setOf_eq] at he
      rcases rbi_fin2_cases e with rfl | rfl
      · rw [hK0] at he; exact absurd he (by simp)
      · rw [h] at he; exact absurd he (by simp)
    have : rbi_cfg true false ∈ rbi_B := hB _ hag
    simp [rbi_B, rbi_cfg] at this
  exact ⟨hK0, hK1⟩








lemma rbi_collision_fst (w1 w2 : Fin 2 → Bool)
    (a0 : w1 0 = false) (a1 : w1 1 = true) (b0 : w2 0 = true) (b1 : w2 1 = false) :
    bglue w1 (rbi_cfg false false) (rbi_cfg false true)
      = bglue w2 (rbi_cfg false true) (rbi_cfg false false) := by
  funext e
  rcases rbi_fin2_cases e with rfl | rfl
  · simp only [bglue, a0, b0, if_true]; rfl
  · simp only [bglue, a1, b1, if_true]; rfl



lemma rbi_collision_snd (w1 w2 : Fin 2 → Bool)
    (a0 : w1 0 = false) (a1 : w1 1 = true) (b0 : w2 0 = true) (b1 : w2 1 = false) :
    bglue w1 (rbi_cfg false true) (rbi_cfg false false)
      = bglue w2 (rbi_cfg false false) (rbi_cfg false true) := by
  funext e
  rcases rbi_fin2_cases e with rfl | rfl
  · simp only [bglue, a0, b0, if_true]; rfl
  · simp only [bglue, a1, b1, if_true]; rfl





lemma rbi_pairs_ne :
    ((rbi_cfg false false, rbi_cfg false true) : ConfigSpace (Fin 2) × ConfigSpace (Fin 2))
      ≠ (rbi_cfg false true, rbi_cfg false false) := by
  intro h
  have : rbi_cfg false false = rbi_cfg false true := congrArg Prod.fst h
  have h1 := congrFun this 1
  simp [rbi_cfg] at h1





theorem rbi_doubleCover_false : ¬ rdc_DoubleCover rbi_A rbi_B := by
  rintro ⟨wit, hwitA, hwitB, hinj⟩
  
  obtain ⟨a0, a1⟩ := rbi_force_FF (wit (rbi_cfg false false))
    (hwitA _ rbi_FF_in_box) (hwitB _ rbi_FF_in_box)
  obtain ⟨b0, b1⟩ := rbi_force_FT (wit (rbi_cfg false true))
    (hwitA _ rbi_FT_in_box) (hwitB _ rbi_FT_in_box)
  
  set p1 : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) :=
    (rbi_cfg false false, rbi_cfg false true) with hp1
  set p2 : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) :=
    (rbi_cfg false true, rbi_cfg false false) with hp2
  have hp1mem : p1 ∈ {p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) |
      p.1 ∈ disjointOccurrence rbi_A rbi_B} := rbi_FF_in_box
  have hp2mem : p2 ∈ {p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) |
      p.1 ∈ disjointOccurrence rbi_A rbi_B} := rbi_FT_in_box
  
  have himg : bfly wit p1 = bfly wit p2 := by
    apply Prod.ext
    · simp only [bfly_fst, hp1, hp2]
      exact rbi_collision_fst _ _ a0 a1 b0 b1
    · simp only [bfly_snd, hp1, hp2]
      exact rbi_collision_snd _ _ a0 a1 b0 b1
  
  exact rbi_pairs_ne (hinj hp1mem hp2mem himg)




theorem rbi_doubleCoverAll_false : ¬ rdc_DoubleCoverAll := by
  intro h
  exact rbi_doubleCover_false (h 2 rbi_A rbi_B)













theorem rbi_box_eq :
    disjointOccurrence rbi_A rbi_B
      = {rbi_cfg false false, rbi_cfg false true} := by
  apply Set.eq_of_subset_of_subset
  · 
    
    rintro ω ⟨K, L, hKL, hAK, hBL⟩
    have hωA : ω ∈ rbi_A := hAK.mem_self
    have hωB : ω ∈ rbi_B := hBL.mem_self
    simp only [rbi_A, Set.mem_setOf_eq] at hωA
    simp only [rbi_B, Set.mem_setOf_eq] at hωB
    
    have hω0 : ω 0 = false := by
      by_contra h; simp only [Bool.not_eq_false] at h
      have h1 : ω 1 ≠ true := fun ht => hωA ⟨h, ht⟩
      have h2 : ω 1 ≠ false := fun hf => hωB ⟨h, hf⟩
      cases hb : ω 1 with
      | false => exact h2 hb
      | true => exact h1 hb
    
    have hext : ω = rbi_cfg (ω 0) (ω 1) := by
      funext i; rcases rbi_fin2_cases i with rfl | rfl <;> rfl
    cases hb : ω 1 with
    | false => left; rw [hext, hω0, hb]
    | true => right; rw [Set.mem_singleton_iff, hext, hω0, hb]
  · intro ω hω
    rcases hω with h | h
    · rw [h]; exact rbi_FF_in_box
    · rw [Set.mem_singleton_iff] at h; rw [h]; exact rbi_FT_in_box

end StatMech
