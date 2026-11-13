/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Fin.Rev
import Mathlib.Order.Fin.Basic

@[expose] public section

section
namespace MetaMathlibExt

private theorem descent_or_ascent (d : ℕ) (σ : Equiv.Perm (Fin (d + 2))) (i : Fin (d + 1)) :
    (σ i.castSucc > σ i.succ) ∨ (σ i.castSucc < σ i.succ) := by
  have hne : (i.castSucc : Fin (d + 2)) ≠ i.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp [Fin.val_castSucc, Fin.val_succ] at hv
  have h : σ i.castSucc ≠ σ i.succ := fun he => hne (σ.injective he)
  rcases lt_or_gt_of_ne h with h1 | h1
  · exact Or.inr h1
  · exact Or.inl h1

private theorem descent_add_ascent (d : ℕ) (σ : Equiv.Perm (Fin (d + 2))) :
    (Finset.univ.filter fun i : Fin (d + 1) => σ i.castSucc > σ i.succ).card +
    (Finset.univ.filter fun i : Fin (d + 1) => σ i.castSucc < σ i.succ).card = d + 1 := by
  have hunion : (Finset.univ.filter fun i : Fin (d + 1) => σ i.castSucc > σ i.succ) ∪
    (Finset.univ.filter fun i : Fin (d + 1) => σ i.castSucc < σ i.succ) = Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_of_true (descent_or_ascent d σ i) trivial
  have hdisj : Disjoint
    (Finset.univ.filter fun i : Fin (d + 1) => σ i.castSucc > σ i.succ)
    (Finset.univ.filter fun i : Fin (d + 1) => σ i.castSucc < σ i.succ) := by
    apply Finset.disjoint_filter.mpr
    intro i _ h1 h2
    exact absurd (lt_trans h2 h1) (lt_irrefl _)
  calc (Finset.univ.filter fun i : Fin (d + 1) => σ i.castSucc > σ i.succ).card +
      (Finset.univ.filter fun i : Fin (d + 1) => σ i.castSucc < σ i.succ).card
      = ((Finset.univ.filter fun i : Fin (d + 1) => σ i.castSucc > σ i.succ) ∪
        (Finset.univ.filter fun i : Fin (d + 1) => σ i.castSucc < σ i.succ)).card := by
          rw [Finset.card_union_of_disjoint hdisj]
    _ = Finset.univ.card := by rw [hunion]
    _ = d + 1 := by simp

-- Permutations with `d` descents have exactly one ascent.
private theorem exactly_one_ascent_of_descent_eq (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (h : (Finset.univ.filter fun i : Fin (d + 1) => σ i.castSucc > σ i.succ).card = d) :
    (Finset.univ.filter fun i : Fin (d + 1) => σ i.castSucc < σ i.succ).card = 1 := by
  have h2 := descent_add_ascent d σ
  omega

private theorem deletion_gap_ne (d : ℕ) (j : Fin (d + 2)) (i : Fin d) :
    j.succAbove i.castSucc ≠ j.succAbove i.succ := by
  apply Fin.succAbove_right_injective.ne
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castSucc, Fin.val_succ] at hv
  omega

private theorem deletion_or (d : ℕ) (σ : Equiv.Perm (Fin (d + 2))) (j : Fin (d + 2))
    (i : Fin d) :
    (σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)) ∨
      (σ (j.succAbove i.castSucc) < σ (j.succAbove i.succ)) := by
  have hne : σ (j.succAbove i.castSucc) ≠ σ (j.succAbove i.succ) :=
    fun he => deletion_gap_ne d j i (σ.injective he)
  rcases lt_or_gt_of_ne hne with h1 | h1
  · exact Or.inr h1
  · exact Or.inl h1

private theorem deletion_add (d : ℕ) (σ : Equiv.Perm (Fin (d + 2))) (j : Fin (d + 2)) :
    (Finset.univ.filter fun i : Fin d =>
        σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)).card +
      (Finset.univ.filter fun i : Fin d =>
        σ (j.succAbove i.castSucc) < σ (j.succAbove i.succ)).card = d := by
  have hunion : (Finset.univ.filter fun i : Fin d =>
        σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)) ∪
      (Finset.univ.filter fun i : Fin d =>
        σ (j.succAbove i.castSucc) < σ (j.succAbove i.succ)) = Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_of_true (deletion_or d σ j i) trivial
  have hdisj : Disjoint
      (Finset.univ.filter fun i : Fin d =>
        σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ))
      (Finset.univ.filter fun i : Fin d =>
        σ (j.succAbove i.castSucc) < σ (j.succAbove i.succ)) := by
    apply Finset.disjoint_filter.mpr
    intro i _ h1 h2
    exact absurd (lt_trans h2 h1) (lt_irrefl _)
  calc (Finset.univ.filter fun i : Fin d =>
          σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)).card +
        (Finset.univ.filter fun i : Fin d =>
          σ (j.succAbove i.castSucc) < σ (j.succAbove i.succ)).card
      = ((Finset.univ.filter fun i : Fin d =>
            σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)) ∪
          (Finset.univ.filter fun i : Fin d =>
            σ (j.succAbove i.castSucc) < σ (j.succAbove i.succ))).card := by
          rw [Finset.card_union_of_disjoint hdisj]
    _ = Finset.univ.card := by rw [hunion]
    _ = d := by simp

private theorem succAbove_val (d : ℕ) (j : Fin (d + 2)) (k : Fin (d + 1)) :
    (j.succAbove k).val = if k.val < j.val then k.val else k.val + 1 := by
  by_cases h : k.val < j.val
  · have hc : k.castSucc < j := by
      rw [Fin.lt_def]
      simp only [Fin.val_castSucc]
      exact h
    rw [Fin.succAbove_of_castSucc_lt _ _ hc]
    simp only [Fin.val_castSucc, h, ↓reduceIte]
  · have hc : ¬ k.castSucc < j := by
      rw [Fin.lt_def]
      simp only [Fin.val_castSucc]
      exact h
    rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hc)]
    simp only [Fin.val_succ, h, ↓reduceIte]

private theorem deletion_consec_of_ne (d : ℕ) (j : Fin (d + 2)) (i : Fin d)
    (h : i.val + 1 ≠ j.val) :
    ∃ k : Fin (d + 1), j.succAbove i.castSucc = k.castSucc ∧
      j.succAbove i.succ = k.succ := by
  have hx : (j.succAbove i.castSucc).val =
      if i.val < j.val then i.val else i.val + 1 := by
    have hv := succAbove_val d j i.castSucc
    simp only [Fin.val_castSucc] at hv
    exact hv
  have hy : (j.succAbove i.succ).val =
      if i.val + 1 < j.val then i.val + 1 else i.val + 2 := by
    have hv := succAbove_val d j i.succ
    simp only [Fin.val_succ] at hv
    exact hv
  have hcases : (j.succAbove i.castSucc).val + 1 = (j.succAbove i.succ).val := by
    by_cases hlt : i.val + 1 < j.val
    · have h1 : i.val < j.val := by omega
      simp only [hx, hy, h1, hlt, ↓reduceIte]
    · have hle : j.val ≤ i.val := by omega
      have h1 : ¬ i.val < j.val := by omega
      have h2 : ¬ i.val + 1 < j.val := hlt
      simp only [hx, hy, h1, h2, ↓reduceIte]
  have hlt : (j.succAbove i.castSucc).val < d + 1 := by
    have hj := (j.succAbove i.succ).isLt
    omega
  let k : Fin (d + 1) := ⟨(j.succAbove i.castSucc).val, hlt⟩
  have hk1 : (k.castSucc).val = (j.succAbove i.castSucc).val := by
    simp only [Fin.val_castSucc, k]
  have hk2 : (k.succ).val = (j.succAbove i.succ).val := by
    simp only [Fin.val_succ, k]
    omega
  refine ⟨k, ?_, ?_⟩
  · exact Fin.ext hk1.symm
  · exact Fin.ext hk2.symm

private theorem deletion_bridge_of_eq (d : ℕ) (j : Fin (d + 2)) (i : Fin d)
    (h : i.val + 1 = j.val) :
    (j.succAbove i.castSucc).val + 1 = j.val ∧
      (j.succAbove i.succ).val = (j.succAbove i.castSucc).val + 2 := by
  have hx : (j.succAbove i.castSucc).val =
      if i.val < j.val then i.val else i.val + 1 := by
    have hv := succAbove_val d j i.castSucc
    simp only [Fin.val_castSucc] at hv
    exact hv
  have hy : (j.succAbove i.succ).val =
      if i.val + 1 < j.val then i.val + 1 else i.val + 2 := by
    have hv := succAbove_val d j i.succ
    simp only [Fin.val_succ] at hv
    exact hv
  have h1 : i.val < j.val := by omega
  have h2 : ¬ i.val + 1 < j.val := by omega
  rw [hx, hy, ite_eq_left h1, ite_eq_right h2]
  constructor
  · omega
  · rfl

private theorem ascent_singleton_of_descent (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (h : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc > σ i.succ).card = d) :
    ∃ a : Fin (d + 1), (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a} := by
  have h1 := exactly_one_ascent_of_descent_eq d σ h
  exact Finset.card_eq_one.mp h1

private theorem descent_of_ne_ascent (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a k : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a}) (hk : k ≠ a) :
    σ k.castSucc > σ k.succ := by
  have hmem : k ∉ Finset.univ.filter (fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) := by
    rw [ha]
    exact fun h => hk (Finset.mem_singleton.mp h)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hmem
  have hne : σ k.castSucc ≠ σ k.succ := by
    have hkk : (k.castSucc : Fin (d + 2)) ≠ k.succ := by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [Fin.val_castSucc, Fin.val_succ] at hv
      omega
    exact fun he => hkk (σ.injective he)
  have hle : σ k.succ ≤ σ k.castSucc := hmem
  have hlt : σ k.succ < σ k.castSucc := lt_of_le_of_ne hle (Ne.symm hne)
  exact hlt

private theorem ascent_of_mem_singleton (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a}) :
    σ a.castSucc < σ a.succ := by
  have hmem : a ∈ Finset.univ.filter (fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) := by
    rw [ha]
    exact Finset.mem_singleton_self a
  exact (Finset.mem_filter.mp hmem).2

private theorem deletion_ascent_of_ne (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1)) (j : Fin (d + 2))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a})
    (hj1 : j ≠ a.castSucc) (hj2 : j ≠ a.succ) :
    ∃ i : Fin d, σ (j.succAbove i.castSucc) < σ (j.succAbove i.succ) := by
  have hasc := ascent_of_mem_singleton d σ a ha
  have hj1' : j.val ≠ a.val := by
    intro he
    apply hj1
    apply Fin.ext
    simp only [Fin.val_castSucc]
    exact he
  have hj2' : j.val ≠ a.val + 1 := by
    intro he
    apply hj2
    apply Fin.ext
    simp only [Fin.val_succ]
    exact he
  by_cases hlt : a.val + 1 < j.val
  · have hlt1 : a.val < d := by
      have hj := j.isLt
      omega
    let i : Fin d := ⟨a.val, hlt1⟩
    have hi1 : i.val = a.val := rfl
    have hx : (j.succAbove i.castSucc).val = a.val := by
      have hv := succAbove_val d j i.castSucc
      simp only [Fin.val_castSucc, hi1] at hv
      have h1 : i.val < j.val := by omega
      rw [hv, ite_eq_left h1]
    have hy : (j.succAbove i.succ).val = a.val + 1 := by
      have hv := succAbove_val d j i.succ
      simp only [Fin.val_succ, hi1] at hv
      have h2 : i.val + 1 < j.val := by omega
      rw [hv, ite_eq_left h2]
    have hxeq : j.succAbove i.castSucc = a.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      exact hx
    have hyeq : j.succAbove i.succ = a.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      exact hy
    exact ⟨i, by rw [hxeq, hyeq]; exact hasc⟩
  · have hle : j.val ≤ a.val + 1 := by omega
    have hle2 : j.val ≤ a.val := by omega
    have hlt2 : j.val < a.val := by
      have := hj1'
      omega
    have hpos : 1 ≤ a.val := by omega
    have hlt3 : a.val - 1 < d := by
      have ha2 := a.isLt
      omega
    let i : Fin d := ⟨a.val - 1, hlt3⟩
    have hi1 : i.val = a.val - 1 := rfl
    have hsucc : i.val + 1 = a.val := by omega
    have hx : (j.succAbove i.castSucc).val = a.val := by
      have hv := succAbove_val d j i.castSucc
      simp only [Fin.val_castSucc, hi1] at hv
      have h1 : ¬ i.val < j.val := by omega
      rw [hv, ite_eq_right h1]
      omega
    have hy : (j.succAbove i.succ).val = a.val + 1 := by
      have hv := succAbove_val d j i.succ
      simp only [Fin.val_succ, hi1] at hv
      have h2 : ¬ i.val + 1 < j.val := by omega
      rw [hv, ite_eq_right h2]
      have h3 : (i.succ).val = a.val := by
        simp only [Fin.val_succ, hi1]
        omega
      omega
    have hxeq : j.succAbove i.castSucc = a.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      exact hx
    have hyeq : j.succAbove i.succ = a.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      exact hy
    exact ⟨i, by rw [hxeq, hyeq]; exact hasc⟩

private theorem deletion_card_lt_of_ascent (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (j : Fin (d + 2)) (i : Fin d)
    (h : σ (j.succAbove i.castSucc) < σ (j.succAbove i.succ)) :
    (Finset.univ.filter fun k : Fin d =>
      σ (j.succAbove k.castSucc) > σ (j.succAbove k.succ)).card < d := by
  have hadd := deletion_add d σ j
  have hmem : i ∈ Finset.univ.filter (fun k : Fin d =>
      σ (j.succAbove k.castSucc) < σ (j.succAbove k.succ)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact h
  have hpos : 0 < (Finset.univ.filter fun k : Fin d =>
      σ (j.succAbove k.castSucc) < σ (j.succAbove k.succ)).card :=
    Finset.card_pos.mpr ⟨i, hmem⟩
  omega

private theorem deletion_card_eq_of_all_descents (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (j : Fin (d + 2))
    (h : ∀ i : Fin d, σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)) :
    (Finset.univ.filter fun k : Fin d =>
      σ (j.succAbove k.castSucc) > σ (j.succAbove k.succ)).card = d := by
  have hfun : (Finset.univ.filter fun k : Fin d =>
      σ (j.succAbove k.castSucc) > σ (j.succAbove k.succ)) = Finset.univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact h i
  rw [hfun]
  simp

private theorem end_first_not_minimal (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a}) (hav : a.val = 0) :
    (Finset.univ.filter fun i : Fin d =>
      σ ((0 : Fin (d + 2)).succAbove i.castSucc) >
        σ ((0 : Fin (d + 2)).succAbove i.succ)).card = d := by
  apply deletion_card_eq_of_all_descents
  intro i
  have hne : i.val + 1 ≠ (0 : Fin (d + 2)).val := by
    simp only [Fin.val_zero]
    omega
  obtain ⟨k, hxeq, hyeq⟩ := deletion_consec_of_ne d 0 i hne
  have hkne : k ≠ a := by
    intro he
    subst he
    have hvk : k.val = ((0 : Fin (d + 2)).succAbove i.castSucc).val := by
      rw [hxeq]
      simp only [Fin.val_castSucc]
    have hx : ((0 : Fin (d + 2)).succAbove i.castSucc).val = i.val + 1 := by
      have hv := succAbove_val d 0 i.castSucc
      simp only [Fin.val_castSucc, Fin.val_zero] at hv
      have h1 : ¬ i.val < 0 := by omega
      simp only [hv, h1, ↓reduceIte]
    omega
  have hdesc := descent_of_ne_ascent d σ a k ha hkne
  rw [hxeq, hyeq]
  exact hdesc

private theorem end_last_not_minimal (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a}) (hav : a.val = d) :
    (Finset.univ.filter fun i : Fin d =>
      σ ((Fin.last (d + 1)).succAbove i.castSucc) >
        σ ((Fin.last (d + 1)).succAbove i.succ)).card = d := by
  apply deletion_card_eq_of_all_descents
  intro i
  have hlast : (Fin.last (d + 1)).val = d + 1 := rfl
  have hne : i.val + 1 ≠ (Fin.last (d + 1)).val := by
    have hi := i.isLt
    omega
  obtain ⟨k, hxeq, hyeq⟩ :=
    deletion_consec_of_ne d (Fin.last (d + 1)) i hne
  have hkne : k ≠ a := by
    intro he
    subst he
    have hvk : k.val = ((Fin.last (d + 1)).succAbove i.castSucc).val := by
      rw [hxeq]
      simp only [Fin.val_castSucc]
    have hx : ((Fin.last (d + 1)).succAbove i.castSucc).val = i.val := by
      have hv := succAbove_val d (Fin.last (d + 1)) i.castSucc
      simp only [Fin.val_castSucc] at hv
      have h1 : i.val < (Fin.last (d + 1)).val := by
        have hi := i.isLt
        have hl := (Fin.last (d + 1)).isLt
        omega
      simp only [hv, h1, ↓reduceIte]
    omega
  have hdesc := descent_of_ne_ascent d σ a k ha hkne
  rw [hxeq, hyeq]
  exact hdesc

private def prevPos (d : ℕ) (a : Fin (d + 1)) (h : 0 < a.val) : Fin (d + 2) :=
  ⟨a.val - 1, by have ha := a.isLt; omega⟩

private def nextPos (d : ℕ) (a : Fin (d + 1)) (h : a.val < d) : Fin (d + 2) :=
  ⟨a.val + 2, by have ha := a.isLt; omega⟩

private theorem prevPos_val (d : ℕ) (a : Fin (d + 1)) (h : 0 < a.val) :
    (prevPos d a h).val = a.val - 1 := rfl

private theorem nextPos_val (d : ℕ) (a : Fin (d + 1)) (h : a.val < d) :
    (nextPos d a h).val = a.val + 2 := rfl

private theorem left_bridge_eq (d : ℕ) (a : Fin (d + 1)) (hpos : 0 < a.val) :
    ∃ i : Fin d, (a.castSucc.succAbove i.castSucc).val = a.val - 1 ∧
      (a.castSucc.succAbove i.succ).val = a.val + 1 ∧
      a.castSucc.succAbove i.castSucc = prevPos d a hpos ∧
      a.castSucc.succAbove i.succ = a.succ := by
  have hlt : a.val - 1 < d := by
    have ha := a.isLt
    omega
  let i : Fin d := ⟨a.val - 1, hlt⟩
  have hi : i.val = a.val - 1 := rfl
  have hbridge : i.val + 1 = (a.castSucc : Fin (d + 2)).val := by
    simp only [Fin.val_castSucc, hi]
    omega
  have hb := deletion_bridge_of_eq d a.castSucc i hbridge
  have hx : (a.castSucc.succAbove i.castSucc).val = a.val - 1 := by
    have h1 := hb.1
    simp only [Fin.val_castSucc] at h1
    omega
  have hy : (a.castSucc.succAbove i.succ).val = a.val + 1 := by
    have h2 := hb.2
    omega
  have hxeq : a.castSucc.succAbove i.castSucc = prevPos d a hpos := by
    apply Fin.ext
    simp only [prevPos_val]
    exact hx
  have hyeq : a.castSucc.succAbove i.succ = a.succ := by
    apply Fin.ext
    simp only [Fin.val_succ]
    exact hy
  exact ⟨i, hx, hy, hxeq, hyeq⟩

private theorem right_bridge_eq (d : ℕ) (a : Fin (d + 1)) (hlt : a.val < d) :
    ∃ i : Fin d, (a.succ.succAbove i.castSucc).val = a.val ∧
      (a.succ.succAbove i.succ).val = a.val + 2 ∧
      a.succ.succAbove i.castSucc = a.castSucc ∧
      a.succ.succAbove i.succ = nextPos d a hlt := by
  let i : Fin d := ⟨a.val, hlt⟩
  have hi : i.val = a.val := rfl
  have hbridge : i.val + 1 = (a.succ : Fin (d + 2)).val := by
    simp only [Fin.val_succ, hi]
  have hb := deletion_bridge_of_eq d a.succ i hbridge
  have hx : (a.succ.succAbove i.castSucc).val = a.val := by
    have h1 := hb.1
    simp only [Fin.val_succ] at h1
    omega
  have hy : (a.succ.succAbove i.succ).val = a.val + 2 := by
    have h2 := hb.2
    omega
  have hxeq : a.succ.succAbove i.castSucc = a.castSucc := by
    apply Fin.ext
    simp only [Fin.val_castSucc]
    exact hx
  have hyeq : a.succ.succAbove i.succ = nextPos d a hlt := by
    apply Fin.ext
    simp only [nextPos_val]
    exact hy
  exact ⟨i, hx, hy, hxeq, hyeq⟩

private theorem left_bridge_ascent_of_minimal (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a})
    (hpos : 0 < a.val)
    (hmin : ∀ j : Fin (d + 2), (Finset.univ.filter fun i : Fin d =>
      σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)).card < d) :
    σ (prevPos d a hpos) < σ a.succ := by
  have hcard := hmin a.castSucc
  have hadd := deletion_add d σ a.castSucc
  have hpos2 : 0 < (Finset.univ.filter fun k : Fin d =>
      σ (a.castSucc.succAbove k.castSucc) <
        σ (a.castSucc.succAbove k.succ)).card := by omega
  obtain ⟨i0, hmem⟩ := Finset.card_pos.mp hpos2
  have hasc0 : σ (a.castSucc.succAbove i0.castSucc) <
      σ (a.castSucc.succAbove i0.succ) :=
    (Finset.mem_filter.mp hmem).2
  by_cases heq : i0.val + 1 = (a.castSucc : Fin (d + 2)).val
  · have hb := deletion_bridge_of_eq d a.castSucc i0 heq
    have hx : (a.castSucc.succAbove i0.castSucc).val = a.val - 1 := by
      have h1 := hb.1
      simp only [Fin.val_castSucc] at h1
      omega
    have hy : (a.castSucc.succAbove i0.succ).val = a.val + 1 := by
      have h2 := hb.2
      omega
    have hxeq : a.castSucc.succAbove i0.castSucc = prevPos d a hpos := by
      apply Fin.ext
      simp only [prevPos_val]
      exact hx
    have hyeq : a.castSucc.succAbove i0.succ = a.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      exact hy
    rw [hxeq, hyeq] at hasc0
    exact hasc0
  · obtain ⟨k, hxeq, hyeq⟩ := deletion_consec_of_ne d a.castSucc i0 heq
    have hkne : k ≠ a := by
      intro he
      have hxeq2 : Fin.succAbove a.castSucc i0.castSucc = a.castSucc := by
        rw [hxeq, he]
      exact Fin.succAbove_ne a.castSucc i0.castSucc hxeq2
    have hdesc := descent_of_ne_ascent d σ a k ha hkne
    rw [hxeq, hyeq] at hasc0
    have hlt2 : σ k.castSucc < σ k.succ := hasc0
    have hgt : σ k.succ < σ k.castSucc := hdesc
    exact absurd (lt_trans hlt2 hgt) (lt_irrefl _)

private theorem right_bridge_ascent_of_minimal (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a})
    (hlt : a.val < d)
    (hmin : ∀ j : Fin (d + 2), (Finset.univ.filter fun i : Fin d =>
      σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)).card < d) :
    σ a.castSucc < σ (nextPos d a hlt) := by
  have hcard := hmin a.succ
  have hadd := deletion_add d σ a.succ
  have hpos2 : 0 < (Finset.univ.filter fun k : Fin d =>
      σ (a.succ.succAbove k.castSucc) <
        σ (a.succ.succAbove k.succ)).card := by omega
  obtain ⟨i0, hmem⟩ := Finset.card_pos.mp hpos2
  have hasc0 : σ (a.succ.succAbove i0.castSucc) <
      σ (a.succ.succAbove i0.succ) :=
    (Finset.mem_filter.mp hmem).2
  by_cases heq : i0.val + 1 = (a.succ : Fin (d + 2)).val
  · have hb := deletion_bridge_of_eq d a.succ i0 heq
    have hx : (a.succ.succAbove i0.castSucc).val = a.val := by
      have h1 := hb.1
      simp only [Fin.val_succ] at h1
      omega
    have hy : (a.succ.succAbove i0.succ).val = a.val + 2 := by
      have h2 := hb.2
      omega
    have hxeq : a.succ.succAbove i0.castSucc = a.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      exact hx
    have hyeq : a.succ.succAbove i0.succ = nextPos d a hlt := by
      apply Fin.ext
      simp only [nextPos_val]
      exact hy
    rw [hxeq, hyeq] at hasc0
    exact hasc0
  · obtain ⟨k, hxeq, hyeq⟩ := deletion_consec_of_ne d a.succ i0 heq
    have hkne : k ≠ a := by
      intro he
      have hyeq2 : Fin.succAbove a.succ i0.succ = a.succ := by
        rw [hyeq, he]
      exact Fin.succAbove_ne a.succ i0.succ hyeq2
    have hdesc := descent_of_ne_ascent d σ a k ha hkne
    rw [hxeq, hyeq] at hasc0
    have hlt2 : σ k.castSucc < σ k.succ := hasc0
    have hgt : σ k.succ < σ k.castSucc := hdesc
    exact absurd (lt_trans hlt2 hgt) (lt_irrefl _)

private theorem minimal_of_bridges (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a})
    (hpos : 0 < a.val) (hlt : a.val < d)
    (hleft : σ (prevPos d a hpos) < σ a.succ)
    (hright : σ a.castSucc < σ (nextPos d a hlt)) :
    ∀ j : Fin (d + 2), (Finset.univ.filter fun i : Fin d =>
      σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)).card < d := by
  intro j
  by_cases hj1 : j = a.castSucc
  · subst hj1
    obtain ⟨i, _, _, hxeq, hyeq⟩ := left_bridge_eq d a hpos
    have hasc : σ (a.castSucc.succAbove i.castSucc) <
        σ (a.castSucc.succAbove i.succ) := by
      rw [hxeq, hyeq]
      exact hleft
    exact deletion_card_lt_of_ascent d σ a.castSucc i hasc
  · by_cases hj2 : j = a.succ
    · subst hj2
      obtain ⟨i, _, _, hxeq, hyeq⟩ := right_bridge_eq d a hlt
      have hasc : σ (a.succ.succAbove i.castSucc) <
          σ (a.succ.succAbove i.succ) := by
        rw [hxeq, hyeq]
        exact hright
      exact deletion_card_lt_of_ascent d σ a.succ i hasc
    · obtain ⟨i, hasc⟩ := deletion_ascent_of_ne d σ a j ha hj1 hj2
      exact deletion_card_lt_of_ascent d σ j i hasc

private def block1Pos (d : ℕ) (a : Fin (d + 1)) (i : Fin (a.val + 1)) :
    Fin (d + 2) :=
  ⟨i.val, by have ha := a.isLt; have hi := i.isLt; omega⟩

private def block2Pos (d : ℕ) (a : Fin (d + 1)) (i : Fin ((d - a.val) + 1)) :
    Fin (d + 2) :=
  ⟨a.val + 1 + i.val, by have ha := a.isLt; have hi := i.isLt; omega⟩

private theorem block1Pos_val (d : ℕ) (a : Fin (d + 1)) (i : Fin (a.val + 1)) :
    (block1Pos d a i).val = i.val := rfl

private theorem block2Pos_val (d : ℕ) (a : Fin (d + 1))
    (i : Fin ((d - a.val) + 1)) :
    (block2Pos d a i).val = a.val + 1 + i.val := rfl

private theorem block1_anti (d : ℕ) (σ : Equiv.Perm (Fin (d + 2))) (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a}) :
    StrictAnti (fun i : Fin (a.val + 1) => σ (block1Pos d a i)) := by
  rw [Fin.strictAnti_iff_succ_lt]
  intro i
  have hi : i.val < a.val := i.isLt
  have hlt : i.val < d + 1 := by
    have ha2 := a.isLt
    omega
  let k : Fin (d + 1) := ⟨i.val, hlt⟩
  have hk : k.val = i.val := rfl
  have hkne : k ≠ a := by
    intro he
    have hv := congrArg Fin.val he
    simp only [hk] at hv
    omega
  have hdesc := descent_of_ne_ascent d σ a k ha hkne
  have e1 : block1Pos d a i.castSucc = k.castSucc := by
    apply Fin.ext
    simp only [block1Pos_val, Fin.val_castSucc, hk]
  have e2 : block1Pos d a i.succ = k.succ := by
    apply Fin.ext
    simp only [block1Pos_val, Fin.val_succ, hk]
  simp only [e1, e2]
  exact hdesc

private theorem block2_anti (d : ℕ) (σ : Equiv.Perm (Fin (d + 2))) (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a}) :
    StrictAnti (fun i : Fin ((d - a.val) + 1) => σ (block2Pos d a i)) := by
  rw [Fin.strictAnti_iff_succ_lt]
  intro i
  have hi : i.val < d - a.val := i.isLt
  have ha2 := a.isLt
  have hlt : a.val + 1 + i.val < d + 1 := by omega
  let k : Fin (d + 1) := ⟨a.val + 1 + i.val, hlt⟩
  have hk : k.val = a.val + 1 + i.val := rfl
  have hkne : k ≠ a := by
    intro he
    have hv := congrArg Fin.val he
    simp only [hk] at hv
    omega
  have hdesc := descent_of_ne_ascent d σ a k ha hkne
  have e1 : block2Pos d a i.castSucc = k.castSucc := by
    apply Fin.ext
    simp only [block2Pos_val, Fin.val_castSucc, hk]
  have e2 : block2Pos d a i.succ = k.succ := by
    apply Fin.ext
    simp only [block2Pos_val, Fin.val_succ, hk]
    have h1 : (i.succ).val = i.val + 1 := Fin.val_succ i
    have h2 : (i.castSucc).val = i.val := Fin.val_castSucc i
    omega
  simp only [e1, e2]
  exact hdesc

private def firstVals (d : ℕ) (σ : Equiv.Perm (Fin (d + 2))) (a : Fin (d + 1)) :
    Finset (Fin (d + 2)) :=
  Finset.image (fun i : Fin (a.val + 1) => σ (block1Pos d a i)) Finset.univ

private def secondVals (d : ℕ) (σ : Equiv.Perm (Fin (d + 2))) (a : Fin (d + 1)) :
    Finset (Fin (d + 2)) :=
  Finset.image (fun i : Fin ((d - a.val) + 1) => σ (block2Pos d a i)) Finset.univ

private theorem block1Pos_inj (d : ℕ) (a : Fin (d + 1)) :
    Function.Injective (block1Pos d a) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [block1Pos_val] at hv
  exact Fin.ext hv

private theorem block2Pos_inj (d : ℕ) (a : Fin (d + 1)) :
    Function.Injective (block2Pos d a) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [block2Pos_val] at hv
  have heq : i.val = j.val := by omega
  exact Fin.ext heq

private theorem firstVals_card (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1)) : (firstVals d σ a).card = a.val + 1 := by
  simp only [firstVals, Finset.card_image_of_injective _ (by
    intro i j h
    exact block1Pos_inj d a (σ.injective h)), Finset.card_univ,
    Fintype.card_fin]

private theorem secondVals_card (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1)) : (secondVals d σ a).card = (d - a.val) + 1 := by
  simp only [secondVals, Finset.card_image_of_injective _ (by
    intro i j h
    exact block2Pos_inj d a (σ.injective h)), Finset.card_univ,
    Fintype.card_fin]

private theorem firstVals_nonempty (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1)) : (firstVals d σ a).Nonempty := by
  have hcard := firstVals_card d σ a
  have hpos : 0 < (firstVals d σ a).card := by omega
  exact Finset.card_pos.mp hpos

private theorem secondVals_nonempty (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1)) : (secondVals d σ a).Nonempty := by
  have hcard := secondVals_card d σ a
  have hpos : 0 < (secondVals d σ a).card := by omega
  exact Finset.card_pos.mp hpos

private theorem firstVals_min (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a}) :
    (firstVals d σ a).min' (firstVals_nonempty d σ a) = σ a.castSucc := by
  have hanti := block1_anti d σ a ha
  have hlast : (block1Pos d a (Fin.last a.val)).val =
      (a.castSucc : Fin (d + 2)).val := by
    simp only [block1Pos_val, Fin.val_castSucc, Fin.val_last]
  have hbeq : block1Pos d a (Fin.last a.val) = a.castSucc := Fin.ext hlast
  have hle : ∀ y ∈ firstVals d σ a, σ (block1Pos d a (Fin.last a.val)) ≤ y := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    rcases lt_or_eq_of_le (Fin.le_last i) with hlt | heq
    · exact le_of_lt (hanti hlt)
    · subst heq
      exact le_refl _
  have hmem : σ (block1Pos d a (Fin.last a.val)) ∈ firstVals d σ a := by
    simp only [firstVals, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨_, rfl⟩
  have hmin_le : (firstVals d σ a).min' (firstVals_nonempty d σ a) ≤
      σ (block1Pos d a (Fin.last a.val)) :=
    Finset.min'_le _ _ hmem
  have hle_min : σ (block1Pos d a (Fin.last a.val)) ≤
      (firstVals d σ a).min' (firstVals_nonempty d σ a) := by
    have hm := Finset.min'_mem (firstVals d σ a) (firstVals_nonempty d σ a)
    exact hle _ hm
  have heq : (firstVals d σ a).min' (firstVals_nonempty d σ a) =
      σ (block1Pos d a (Fin.last a.val)) :=
    le_antisymm hmin_le hle_min
  rw [heq, hbeq]

private theorem secondVals_max (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a}) :
    (secondVals d σ a).max' (secondVals_nonempty d σ a) = σ a.succ := by
  have hanti := block2_anti d σ a ha
  have hz : (block2Pos d a 0).val = (a.succ : Fin (d + 2)).val := by
    simp only [block2Pos_val, Fin.val_succ, Fin.val_zero]
  have hbeq : block2Pos d a 0 = a.succ := Fin.ext hz
  have hge : ∀ y ∈ secondVals d σ a, y ≤ σ (block2Pos d a 0) := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    rcases eq_or_lt_of_le (Fin.zero_le i) with heq | hlt
    · subst heq
      exact le_refl _
    · exact le_of_lt (hanti hlt)
  have hmem : σ (block2Pos d a 0) ∈ secondVals d σ a := by
    simp only [secondVals, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨0, rfl⟩
  have hmax_ge : σ (block2Pos d a 0) ≤
      (secondVals d σ a).max' (secondVals_nonempty d σ a) :=
    Finset.le_max' _ _ hmem
  have hge_max : (secondVals d σ a).max' (secondVals_nonempty d σ a) ≤
      σ (block2Pos d a 0) := by
    have hm := Finset.max'_mem (secondVals d σ a) (secondVals_nonempty d σ a)
    exact hge _ hm
  have heq : (secondVals d σ a).max' (secondVals_nonempty d σ a) =
      σ (block2Pos d a 0) :=
    le_antisymm hge_max hmax_ge
  rw [heq, hbeq]

private def topSmall (d : ℕ) (a : Fin (d + 1)) (hpos : 0 < a.val) :
    Finset (Fin (d + 2)) :=
  Finset.Ici ⟨d + 2 - a.val, by have ha := a.isLt; omega⟩

private def topLarge (d : ℕ) (a : Fin (d + 1)) : Finset (Fin (d + 2)) :=
  Finset.Ici ⟨d - a.val, by omega⟩

private theorem topSmall_card (d : ℕ) (a : Fin (d + 1)) (hpos : 0 < a.val) :
    (topSmall d a hpos).card = a.val := by
  simp only [topSmall, Fin.card_Ici]
  have ha := a.isLt
  omega

private theorem topLarge_card (d : ℕ) (a : Fin (d + 1)) :
    (topLarge d a).card = a.val + 2 := by
  simp only [topLarge, Fin.card_Ici]
  have ha := a.isLt
  omega

private def exclA (d : ℕ) (a : Fin (d + 1)) (hpos : 0 < a.val) :
    Finset (Finset (Fin (d + 2))) :=
  (Finset.powersetCard (a.val + 1) Finset.univ).filter
    (fun L => topSmall d a hpos ⊆ L)

private def exclB (d : ℕ) (a : Fin (d + 1)) :
    Finset (Finset (Fin (d + 2))) :=
  (Finset.powersetCard (a.val + 1) Finset.univ).filter
    (fun L => L ⊆ topLarge d a)

private theorem exclA_card (d : ℕ) (a : Fin (d + 1)) (hpos : 0 < a.val) :
    (exclA d a hpos).card = d + 2 - a.val := by
  let t1 : Fin (d + 2) := ⟨d + 2 - a.val, by have ha := a.isLt; omega⟩
  have htop : topSmall d a hpos = Finset.Ici t1 := rfl
  have hIio_card : (Finset.Iio t1).card = d + 2 - a.val := by
    simp only [Fin.card_Iio]
    rfl
  have himg : exclA d a hpos =
      Finset.image (fun m : Fin (d + 2) => insert m (topSmall d a hpos))
        (Finset.Iio t1) := by
    ext L
    simp only [exclA, Finset.mem_filter, Finset.mem_powersetCard,
      Finset.mem_image, Finset.mem_Iio]
    constructor
    · intro h
      obtain ⟨⟨hsub, hcard⟩, htopsub⟩ := h
      have hsdiff : ((L \ topSmall d a hpos).card) = 1 := by
        have h1 := topSmall_card d a hpos
        have h2 := Finset.card_sdiff_of_subset htopsub
        omega
      obtain ⟨m, hm⟩ := Finset.card_eq_one.mp hsdiff
      have hmem : m ∈ L ∧ m ∉ topSmall d a hpos := by
        have hmem' : m ∈ L \ topSmall d a hpos := by
          rw [hm]
          exact Finset.mem_singleton_self m
        exact Finset.mem_sdiff.mp hmem'
      have hlt : m < t1 := by
        have hni : m ∉ Finset.Ici t1 := by
          rw [← htop]
          exact hmem.2
        simp only [Finset.mem_Ici, not_le] at hni
        exact hni
      have heq : L = insert m (topSmall d a hpos) := by
        ext x
        simp only [Finset.mem_insert]
        constructor
        · intro hx
          by_cases hx2 : x ∈ topSmall d a hpos
          · exact Or.inr hx2
          · have hx3 : x ∈ L \ topSmall d a hpos :=
              Finset.mem_sdiff.mpr ⟨hx, hx2⟩
            rw [hm] at hx3
            have := Finset.mem_singleton.mp hx3
            exact Or.inl this
        · intro hx
          rcases hx with rfl | hx2
          · exact hmem.1
          · exact htopsub hx2
      exact ⟨m, hlt, heq.symm⟩
    · intro h
      obtain ⟨m, hlt, rfl⟩ := h
      have hni : m ∉ topSmall d a hpos := by
        rw [htop]
        simp only [Finset.mem_Ici, not_le]
        exact hlt
      have hcard : (insert m (topSmall d a hpos)).card = a.val + 1 := by
        rw [Finset.card_insert_of_notMem hni, topSmall_card d a hpos]
      have hsub : insert m (topSmall d a hpos) ⊆ Finset.univ :=
        Finset.subset_univ _
      exact ⟨⟨hsub, hcard⟩, Finset.subset_insert m _⟩
  rw [himg]
  have hinj : Set.InjOn (fun m : Fin (d + 2) => insert m (topSmall d a hpos))
      (Finset.Iio t1) := by
    intro m1 hm1 m2 hm2 h
    have h1 : m1 ∉ topSmall d a hpos := by
      rw [htop]
      simp only [Finset.mem_Ici, not_le]
      exact Finset.mem_Iio.mp hm1
    have h' : insert m1 (topSmall d a hpos) = insert m2 (topSmall d a hpos) := h
    have hmem : m1 ∈ insert m2 (topSmall d a hpos) := by
      rw [← h']
      exact Finset.mem_insert_self m1 _
    rcases Finset.mem_insert.mp hmem with rfl | hmem2
    · rfl
    · exact absurd hmem2 h1
  have hcard := Finset.card_image_of_injOn hinj
  rw [hcard, hIio_card]

private theorem exclB_card (d : ℕ) (a : Fin (d + 1)) :
    (exclB d a).card = a.val + 2 := by
  have himg : exclB d a =
      Finset.image (fun M : Fin (d + 2) => (topLarge d a).erase M)
        (topLarge d a) := by
    ext L
    simp only [exclB, Finset.mem_filter, Finset.mem_powersetCard,
      Finset.mem_image]
    constructor
    · intro h
      obtain ⟨⟨hsub, hcard⟩, hsub2⟩ := h
      have hsdiff : (((topLarge d a) \ L).card) = 1 := by
        have h1 := topLarge_card d a
        have h2 := Finset.card_sdiff_of_subset hsub2
        omega
      obtain ⟨M, hM⟩ := Finset.card_eq_one.mp hsdiff
      have hmem : M ∈ topLarge d a ∧ M ∉ L := by
        have hmem' : M ∈ topLarge d a \ L := by
          rw [hM]
          exact Finset.mem_singleton_self M
        exact Finset.mem_sdiff.mp hmem'
      have heq : L = (topLarge d a).erase M := by
        ext x
        simp only [Finset.mem_erase]
        constructor
        · intro hx
          exact ⟨fun he => hmem.2 (he ▸ hx), hsub2 hx⟩
        · intro hx
          obtain ⟨hne, hx2⟩ := hx
          by_cases hx3 : x ∈ L
          · exact hx3
          · have hx4 : x ∈ topLarge d a \ L :=
              Finset.mem_sdiff.mpr ⟨hx2, hx3⟩
            rw [hM] at hx4
            have := Finset.mem_singleton.mp hx4
            exact absurd this hne
      exact ⟨M, hmem.1, heq.symm⟩
    · intro h
      obtain ⟨M, hM, rfl⟩ := h
      have hcard : ((topLarge d a).erase M).card = a.val + 1 := by
        rw [Finset.card_erase_of_mem hM, topLarge_card d a]
        omega
      have hsub : (topLarge d a).erase M ⊆ Finset.univ :=
        Finset.subset_univ _
      exact ⟨⟨hsub, hcard⟩, Finset.erase_subset _ _⟩
  rw [himg]
  have hinj : Set.InjOn (fun M : Fin (d + 2) => (topLarge d a).erase M)
      (topLarge d a) := by
    intro M1 hM1 M2 hM2 h
    have h' : (topLarge d a).erase M1 = (topLarge d a).erase M2 := h
    have hni : M1 ∉ (topLarge d a).erase M2 := by
      rw [← h']
      intro hm
      have := Finset.mem_erase.mp hm
      exact this.1 rfl
    have hmem1 : M1 ∈ topLarge d a := Finset.mem_coe.mp hM1
    have hne : ¬ M1 ≠ M2 := by
      intro hne2
      exact hni (Finset.mem_erase.mpr ⟨hne2, hmem1⟩)
    exact not_not.mp hne
  have hcard := Finset.card_image_of_injOn hinj
  rw [hcard, topLarge_card d a]

private theorem topSmall_subset_topLarge (d : ℕ) (a : Fin (d + 1))
    (hpos : 0 < a.val) : topSmall d a hpos ⊆ topLarge d a := by
  intro x hx
  simp only [topSmall, topLarge, Finset.mem_Ici] at hx ⊢
  have ha := a.isLt
  have hle : (⟨d - a.val, by omega⟩ : Fin (d + 2)) ≤
      (⟨d + 2 - a.val, by have ha := a.isLt; omega⟩ : Fin (d + 2)) := by
    simp only [Fin.le_def]
    omega
  exact le_trans hle hx

private theorem exclInter_card (d : ℕ) (a : Fin (d + 1)) (hpos : 0 < a.val) :
    (exclA d a hpos ∩ exclB d a).card = 2 := by
  have hsub := topSmall_subset_topLarge d a hpos
  have hsdiff : ((topLarge d a \ topSmall d a hpos).card) = 2 := by
    have h1 := topLarge_card d a
    have h2 := topSmall_card d a hpos
    have h3 := Finset.card_sdiff_of_subset hsub
    omega
  have himg : exclA d a hpos ∩ exclB d a =
      Finset.image (fun x : Fin (d + 2) => insert x (topSmall d a hpos))
        (topLarge d a \ topSmall d a hpos) := by
    ext L
    simp only [Finset.mem_inter, exclA, exclB, Finset.mem_filter,
      Finset.mem_powersetCard, Finset.mem_image, Finset.mem_sdiff]
    constructor
    · intro h
      obtain ⟨⟨⟨hsub, hcard⟩, hsmall⟩, ⟨⟨_, _⟩, hlarge⟩⟩ := h
      have hsdiff2 : ((L \ topSmall d a hpos).card) = 1 := by
        have h1 := topSmall_card d a hpos
        have h2 := Finset.card_sdiff_of_subset hsmall
        omega
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hsdiff2
      have hmem : x ∈ L ∧ x ∉ topSmall d a hpos := by
        have hmem' : x ∈ L \ topSmall d a hpos := by
          rw [hx]
          exact Finset.mem_singleton_self x
        exact Finset.mem_sdiff.mp hmem'
      have hxlarge : x ∈ topLarge d a := hlarge hmem.1
      have heq : L = insert x (topSmall d a hpos) := by
        ext y
        simp only [Finset.mem_insert]
        constructor
        · intro hy
          by_cases hy2 : y ∈ topSmall d a hpos
          · exact Or.inr hy2
          · have hy3 : y ∈ L \ topSmall d a hpos :=
              Finset.mem_sdiff.mpr ⟨hy, hy2⟩
            rw [hx] at hy3
            have := Finset.mem_singleton.mp hy3
            exact Or.inl this
        · intro hy
          rcases hy with rfl | hy2
          · exact hmem.1
          · exact hsmall hy2
      exact ⟨x, ⟨hxlarge, hmem.2⟩, heq.symm⟩
    · intro h
      obtain ⟨x, ⟨hxlarge, hsmall2⟩, rfl⟩ := h
      have hni : x ∉ topSmall d a hpos := hsmall2
      have hcard : (insert x (topSmall d a hpos)).card = a.val + 1 := by
        rw [Finset.card_insert_of_notMem hni, topSmall_card d a hpos]
      have hsub : insert x (topSmall d a hpos) ⊆ Finset.univ :=
        Finset.subset_univ _
      have hsmall : topSmall d a hpos ⊆ insert x (topSmall d a hpos) :=
        Finset.subset_insert x _
      have hlarge : insert x (topSmall d a hpos) ⊆ topLarge d a := by
        intro y hy
        simp only [Finset.mem_insert] at hy
        rcases hy with rfl | hy2
        · exact hxlarge
        · exact topSmall_subset_topLarge d a hpos hy2
      exact ⟨⟨⟨hsub, hcard⟩, hsmall⟩, ⟨⟨hsub, hcard⟩, hlarge⟩⟩
  rw [himg]
  have hinj : Set.InjOn (fun x : Fin (d + 2) => insert x (topSmall d a hpos))
      (↑(topLarge d a \ topSmall d a hpos) : Set (Fin (d + 2))) := by
    intro x1 hx1 x2 hx2 h
    have hx1' : x1 ∈ topLarge d a \ topSmall d a hpos :=
      Finset.mem_coe.mp hx1
    have h1 : x1 ∉ topSmall d a hpos := (Finset.mem_sdiff.mp hx1').2
    have h' : insert x1 (topSmall d a hpos) = insert x2 (topSmall d a hpos) := h
    have hmem : x1 ∈ insert x2 (topSmall d a hpos) := by
      rw [← h']
      exact Finset.mem_insert_self x1 _
    rcases Finset.mem_insert.mp hmem with rfl | hmem2
    · rfl
    · exact absurd hmem2 h1
  have hcard := Finset.card_image_of_injOn hinj
  rw [hcard, hsdiff]

private theorem exclUnion_card (d : ℕ) (a : Fin (d + 1)) (hpos : 0 < a.val) :
    (exclA d a hpos ∪ exclB d a).card = d + 2 := by
  have hA := exclA_card d a hpos
  have hB := exclB_card d a
  have hI := exclInter_card d a hpos
  have hunion := Finset.card_union_add_card_inter (exclA d a hpos) (exclB d a)
  have ha := a.isLt
  omega

private theorem vals_disjoint_union (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1)) :
    Disjoint (firstVals d σ a) (secondVals d σ a) ∧
      firstVals d σ a ∪ secondVals d σ a = Finset.univ := by
  have hdisj : Disjoint (firstVals d σ a) (secondVals d σ a) := by
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    obtain ⟨i1, _, rfl⟩ := Finset.mem_image.mp hy1
    obtain ⟨i2, _, heq2⟩ := Finset.mem_image.mp hy2
    have heq := σ.injective heq2.symm
    have hv := congrArg Fin.val heq
    simp only [block1Pos_val, block2Pos_val] at hv
    have hi1 := i1.isLt
    have hi2 := i2.isLt
    have ha := a.isLt
    omega
  have hunion : firstVals d σ a ∪ secondVals d σ a = Finset.univ := by
    ext y
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    have hj : ∃ j : Fin (d + 2), σ j = y := ⟨σ.symm y, by simp⟩
    obtain ⟨j, rfl⟩ := hj
    by_cases hle : j.val ≤ a.val
    · have hlt : j.val < a.val + 1 := by omega
      let i : Fin (a.val + 1) := ⟨j.val, hlt⟩
      have heq : block1Pos d a i = j := by
        apply Fin.ext
        simp only [block1Pos_val]
        rfl
      exact Or.inl (by
        simp only [firstVals, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨i, by rw [heq]⟩)
    · have hgt : a.val < j.val := by omega
      have hle2 : a.val + 1 ≤ j.val := by omega
      have hlt2 : j.val - (a.val + 1) < (d - a.val) + 1 := by
        have hj2 := j.isLt
        have ha2 := a.isLt
        omega
      let i : Fin ((d - a.val) + 1) := ⟨j.val - (a.val + 1), hlt2⟩
      have heq : block2Pos d a i = j := by
        apply Fin.ext
        simp only [block2Pos_val]
        have hi : i.val = j.val - (a.val + 1) := rfl
        omega
      exact Or.inr (by
        simp only [secondVals, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨i, by rw [heq]⟩)
  exact ⟨hdisj, hunion⟩

private theorem prevPos_eq_block1 (d : ℕ) (a : Fin (d + 1)) (hpos : 0 < a.val) :
    prevPos d a hpos = block1Pos d a ⟨a.val - 1, by omega⟩ := by
  apply Fin.ext
  simp only [prevPos_val, block1Pos_val]

private theorem nextPos_eq_block2 (d : ℕ) (a : Fin (d + 1)) (hlt : a.val < d) :
    nextPos d a hlt = block2Pos d a ⟨1, by omega⟩ := by
  apply Fin.ext
  simp only [nextPos_val, block2Pos_val]

private theorem left_failure_of_memA (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a})
    (hpos : 0 < a.val) (hlt : a.val < d)
    (hA : firstVals d σ a ∈ exclA d a hpos) :
    σ a.succ < σ (prevPos d a hpos) := by
  have htopsub : topSmall d a hpos ⊆ firstVals d σ a := by
    simp only [exclA, Finset.mem_filter] at hA
    exact hA.2
  have hcardL := firstVals_card d σ a
  have hsdiff : (((firstVals d σ a) \ topSmall d a hpos).card) = 1 := by
    have h1 := topSmall_card d a hpos
    have h2 := Finset.card_sdiff_of_subset htopsub
    omega
  obtain ⟨m, hm⟩ := Finset.card_eq_one.mp hsdiff
  have hmem : m ∈ firstVals d σ a ∧ m ∉ topSmall d a hpos := by
    have hmem' : m ∈ firstVals d σ a \ topSmall d a hpos := by
      rw [hm]
      exact Finset.mem_singleton_self m
    exact Finset.mem_sdiff.mp hmem'
  have heqL : firstVals d σ a = insert m (topSmall d a hpos) := by
    ext y
    simp only [Finset.mem_insert]
    constructor
    · intro hy
      by_cases hy2 : y ∈ topSmall d a hpos
      · exact Or.inr hy2
      · have hy3 : y ∈ firstVals d σ a \ topSmall d a hpos :=
          Finset.mem_sdiff.mpr ⟨hy, hy2⟩
        rw [hm] at hy3
        have := Finset.mem_singleton.mp hy3
        exact Or.inl this
    · intro hy
      rcases hy with rfl | hy2
      · exact hmem.1
      · exact htopsub hy2
  have hmin_eq : (firstVals d σ a).min' (firstVals_nonempty d σ a) = m := by
    have hle : ∀ y ∈ firstVals d σ a, m ≤ y := by
      intro y hy
      rw [heqL] at hy
      rcases Finset.mem_insert.mp hy with rfl | hy2
      · exact le_refl _
      · have hmt : m < (⟨d + 2 - a.val, by have ha := a.isLt; omega⟩ :
            Fin (d + 2)) := by
          have hni : m ∉ Finset.Ici (⟨d + 2 - a.val, by
            have ha := a.isLt; omega⟩ : Fin (d + 2)) := by
            have : topSmall d a hpos =
                Finset.Ici (⟨d + 2 - a.val, by
                  have ha := a.isLt; omega⟩ : Fin (d + 2)) := rfl
            rw [this] at hmem
            exact hmem.2
          simp only [Finset.mem_Ici, not_le] at hni
          exact hni
        have hyt : (⟨d + 2 - a.val, by have ha := a.isLt; omega⟩ :
            Fin (d + 2)) ≤ y := by
          have : y ∈ Finset.Ici (⟨d + 2 - a.val, by
            have ha := a.isLt; omega⟩ : Fin (d + 2)) := by
            have : topSmall d a hpos =
                Finset.Ici (⟨d + 2 - a.val, by
                  have ha := a.isLt; omega⟩ : Fin (d + 2)) := rfl
            rw [this] at hy2
            exact hy2
          simp only [Finset.mem_Ici] at this
          exact this
        exact le_of_lt (lt_of_lt_of_le hmt hyt)
    have h1 : (firstVals d σ a).min' (firstVals_nonempty d σ a) ≤ m :=
      Finset.min'_le _ _ hmem.1
    have h2 : m ≤ (firstVals d σ a).min' (firstVals_nonempty d σ a) := by
      have hm2 := Finset.min'_mem (firstVals d σ a) (firstVals_nonempty d σ a)
      exact hle _ hm2
    exact le_antisymm h1 h2
  have hanti1 := block1_anti d σ a ha
  have hprev_mem : σ (prevPos d a hpos) ∈ firstVals d σ a := by
    have heq2 := prevPos_eq_block1 d a hpos
    rw [heq2]
    simp only [firstVals, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨a.val - 1, by omega⟩, rfl⟩
  have hprev_ne : σ (prevPos d a hpos) ≠ m := by
    have hlt_idx : (⟨a.val - 1, by omega⟩ : Fin (a.val + 1)) < Fin.last a.val := by
      simp only [Fin.lt_def, Fin.val_last]
      omega
    have hlt_val : σ (block1Pos d a (Fin.last a.val)) <
        σ (block1Pos d a ⟨a.val - 1, by omega⟩) := hanti1 hlt_idx
    have hmin2 := firstVals_min d σ a ha
    have hbeq : block1Pos d a (Fin.last a.val) = a.castSucc := by
      apply Fin.ext
      simp only [block1Pos_val, Fin.val_castSucc, Fin.val_last]
    rw [hbeq] at hlt_val
    have heq2 := prevPos_eq_block1 d a hpos
    rw [← heq2] at hlt_val
    have hmin3 : (firstVals d σ a).min' (firstVals_nonempty d σ a) =
        σ a.castSucc := hmin2
    rw [hmin_eq] at hmin3
    omega
  have hprev_top : σ (prevPos d a hpos) ∈ topSmall d a hpos := by
    have hmem2 : σ (prevPos d a hpos) ∈ insert m (topSmall d a hpos) := by
      rw [← heqL]
      exact hprev_mem
    rcases Finset.mem_insert.mp hmem2 with heq | hmem3
    · exact absurd heq hprev_ne
    · exact hmem3
  have hmax_mem : σ a.succ ∈ secondVals d σ a := by
    have hmax_eq := secondVals_max d σ a ha
    rw [← hmax_eq]
    exact Finset.max'_mem _ _
  have hdisj := (vals_disjoint_union d σ a).1
  have hdisj2 : Disjoint (topSmall d a hpos) (secondVals d σ a) :=
    Disjoint.mono htopsub (le_refl _) hdisj
  have hmax_ntop : σ a.succ ∉ topSmall d a hpos := by
    have := Finset.disjoint_right.mp hdisj2 hmax_mem
    exact this
  have hlt_max : σ a.succ < (⟨d + 2 - a.val, by
      have ha := a.isLt; omega⟩ : Fin (d + 2)) := by
    have hni : σ a.succ ∉ Finset.Ici (⟨d + 2 - a.val, by
        have ha := a.isLt; omega⟩ : Fin (d + 2)) := by
      have : topSmall d a hpos =
          Finset.Ici (⟨d + 2 - a.val, by
            have ha := a.isLt; omega⟩ : Fin (d + 2)) := rfl
      rw [this] at hmax_ntop
      exact hmax_ntop
    simp only [Finset.mem_Ici, not_le] at hni
    exact hni
  have hge_prev : (⟨d + 2 - a.val, by have ha := a.isLt; omega⟩ :
      Fin (d + 2)) ≤ σ (prevPos d a hpos) := by
    have : σ (prevPos d a hpos) ∈ Finset.Ici (⟨d + 2 - a.val, by
        have ha := a.isLt; omega⟩ : Fin (d + 2)) := by
      have : topSmall d a hpos =
          Finset.Ici (⟨d + 2 - a.val, by
            have ha := a.isLt; omega⟩ : Fin (d + 2)) := rfl
      rw [this] at hprev_top
      exact hprev_top
    simp only [Finset.mem_Ici] at this
    exact this
  exact lt_of_lt_of_le hlt_max hge_prev

private theorem right_failure_of_memB (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a})
    (hpos : 0 < a.val) (hlt : a.val < d)
    (hB : firstVals d σ a ∈ exclB d a) :
    σ (nextPos d a hlt) < σ a.castSucc := by
  have hsubL : firstVals d σ a ⊆ topLarge d a := by
    simp only [exclB, Finset.mem_filter] at hB
    exact hB.2
  have hdisjU := vals_disjoint_union d σ a
  have hcompl : secondVals d σ a = (firstVals d σ a)ᶜ := by
    ext y
    simp only [Finset.mem_compl]
    constructor
    · intro hy
      have := Finset.disjoint_right.mp hdisjU.1 hy
      exact this
    · intro hy
      have hun : y ∈ firstVals d σ a ∪ secondVals d σ a := by
        rw [hdisjU.2]
        exact Finset.mem_univ y
      simp only [Finset.mem_union] at hun
      rcases hun with h1 | h2
      · exact absurd h1 hy
      · exact h2
  have hbot_sub : Finset.Iio (⟨d - a.val, by omega⟩ : Fin (d + 2)) ⊆
      secondVals d σ a := by
    intro y hy
    simp only [Finset.mem_Iio] at hy
    rw [hcompl]
    simp only [Finset.mem_compl]
    intro hyL
    have hyT : y ∈ topLarge d a := hsubL hyL
    simp only [topLarge, Finset.mem_Ici] at hyT
    have hle : (⟨d - a.val, by omega⟩ : Fin (d + 2)) ≤ y := hyT
    exact absurd (lt_of_lt_of_le hy hle) (lt_irrefl _)
  have hcardR := secondVals_card d σ a
  have hcardB : (Finset.Iio (⟨d - a.val, by omega⟩ : Fin (d + 2))).card =
      d - a.val := by
    simp only [Fin.card_Iio]
  have hsdiff : ((secondVals d σ a \
      Finset.Iio (⟨d - a.val, by omega⟩ : Fin (d + 2))).card) = 1 := by
    have h2 := Finset.card_sdiff_of_subset hbot_sub
    omega
  obtain ⟨M, hM⟩ := Finset.card_eq_one.mp hsdiff
  have hmemM : M ∈ secondVals d σ a ∧
      M ∉ Finset.Iio (⟨d - a.val, by omega⟩ : Fin (d + 2)) := by
    have hmem' : M ∈ secondVals d σ a \
        Finset.Iio (⟨d - a.val, by omega⟩ : Fin (d + 2)) := by
      rw [hM]
      exact Finset.mem_singleton_self M
    exact Finset.mem_sdiff.mp hmem'
  have heqR : secondVals d σ a =
      insert M (Finset.Iio (⟨d - a.val, by omega⟩ : Fin (d + 2))) := by
    ext y
    simp only [Finset.mem_insert]
    constructor
    · intro hy
      by_cases hy2 : y ∈ Finset.Iio (⟨d - a.val, by omega⟩ : Fin (d + 2))
      · exact Or.inr hy2
      · have hy3 : y ∈ secondVals d σ a \
            Finset.Iio (⟨d - a.val, by omega⟩ : Fin (d + 2)) :=
          Finset.mem_sdiff.mpr ⟨hy, hy2⟩
        rw [hM] at hy3
        have := Finset.mem_singleton.mp hy3
        exact Or.inl this
    · intro hy
      rcases hy with rfl | hy2
      · exact hmemM.1
      · exact hbot_sub hy2
  have hMge : (⟨d - a.val, by omega⟩ : Fin (d + 2)) ≤ M := by
    have hni := hmemM.2
    simp only [Finset.mem_Iio, not_lt] at hni
    exact hni
  have hmax_eq : M =
      (secondVals d σ a).max' (secondVals_nonempty d σ a) := by
    have hle : ∀ y ∈ secondVals d σ a, y ≤ M := by
      intro y hy
      rw [heqR] at hy
      rcases Finset.mem_insert.mp hy with rfl | hy2
      · exact le_refl _
      · have hlt : y < (⟨d - a.val, by omega⟩ : Fin (d + 2)) :=
          Finset.mem_Iio.mp hy2
        exact le_of_lt (lt_of_lt_of_le hlt hMge)
    have h1 : M ≤ (secondVals d σ a).max' (secondVals_nonempty d σ a) :=
      Finset.le_max' _ _ hmemM.1
    have h2 : (secondVals d σ a).max' (secondVals_nonempty d σ a) ≤ M := by
      have hm := Finset.max'_mem (secondVals d σ a) (secondVals_nonempty d σ a)
      exact hle _ hm
    exact le_antisymm h1 h2
  have hanti2 := block2_anti d σ a ha
  have hnext_mem : σ (nextPos d a hlt) ∈ secondVals d σ a := by
    have heq2 := nextPos_eq_block2 d a hlt
    rw [heq2]
    simp only [secondVals, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨1, by omega⟩, rfl⟩
  have hnext_ne : σ (nextPos d a hlt) ≠ M := by
    have hlt_idx : (0 : Fin ((d - a.val) + 1)) < ⟨1, by omega⟩ := by
      simp only [Fin.lt_def, Fin.val_zero]
      omega
    have hlt_val : σ (block2Pos d a ⟨1, by omega⟩) <
        σ (block2Pos d a 0) := hanti2 hlt_idx
    have heq2 := nextPos_eq_block2 d a hlt
    have hz : block2Pos d a (0 : Fin ((d - a.val) + 1)) = a.succ := by
      apply Fin.ext
      simp only [block2Pos_val, Fin.val_succ, Fin.val_zero]
    rw [← heq2] at hlt_val
    rw [hz] at hlt_val
    have hmax2 := secondVals_max d σ a ha
    rw [← hmax_eq] at hmax2
    rw [hmax2]
    exact ne_of_lt hlt_val
  have hnext_bot : σ (nextPos d a hlt) ∈
      Finset.Iio (⟨d - a.val, by omega⟩ : Fin (d + 2)) := by
    have hmem2 : σ (nextPos d a hlt) ∈
        insert M (Finset.Iio (⟨d - a.val, by omega⟩ : Fin (d + 2))) := by
      rw [← heqR]
      exact hnext_mem
    rcases Finset.mem_insert.mp hmem2 with heq | hmem3
    · exact absurd heq hnext_ne
    · exact hmem3
  have hmin_mem : (firstVals d σ a).min' (firstVals_nonempty d σ a) ∈
      topLarge d a := hsubL (Finset.min'_mem _ _)
  have hmin_ge : (⟨d - a.val, by omega⟩ : Fin (d + 2)) ≤
      (firstVals d σ a).min' (firstVals_nonempty d σ a) := by
    have : (firstVals d σ a).min' (firstVals_nonempty d σ a) ∈
        Finset.Ici (⟨d - a.val, by omega⟩ : Fin (d + 2)) := by
      have : topLarge d a =
          Finset.Ici (⟨d - a.val, by omega⟩ : Fin (d + 2)) := rfl
      rw [this] at hmin_mem
      exact hmin_mem
    simp only [Finset.mem_Ici] at this
    exact this
  have hnext_lt : σ (nextPos d a hlt) <
      (⟨d - a.val, by omega⟩ : Fin (d + 2)) :=
    Finset.mem_Iio.mp hnext_bot
  have hmin_eq := firstVals_min d σ a ha
  calc σ (nextPos d a hlt)
      < (⟨d - a.val, by omega⟩ : Fin (d + 2)) := hnext_lt
    _ ≤ (firstVals d σ a).min' (firstVals_nonempty d σ a) := hmin_ge
    _ = σ a.castSucc := hmin_eq

private theorem mpe_prev_le_threshold (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a})
    (hpos : 0 < a.val) :
    (σ (prevPos d a hpos)).val ≤ d + 2 - a.val := by
  let s := Finset.image
    (fun i : Fin a.val => σ (block1Pos d a i.castSucc)) Finset.univ
  have hcard : s.card = a.val := by
    rw [Finset.card_image_of_injective]
    · simp only [Finset.card_univ, Fintype.card_fin]
    · intro i j hij
      apply Fin.ext
      have hv := congrArg Fin.val (block1Pos_inj d a (σ.injective hij))
      simpa only [Fin.val_castSucc] using hv
  have hsub : s ⊆ Finset.Ici (σ (prevPos d a hpos)) := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    simp only [Finset.mem_Ici]
    have hle : i.castSucc ≤ (⟨a.val - 1, by omega⟩ : Fin (a.val + 1)) := by
      change i.val ≤ a.val - 1
      omega
    rw [prevPos_eq_block1 d a hpos]
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact le_of_lt (block1_anti d σ a ha hlt)
    · rw [heq]
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  simp only [Fin.card_Ici] at hle
  omega

private theorem mpe_mem_exclA_of_left_failure (d : ℕ)
    (σ : Equiv.Perm (Fin (d + 2))) (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a})
    (hpos : 0 < a.val)
    (hfail : σ a.succ < σ (prevPos d a hpos)) :
    firstVals d σ a ∈ exclA d a hpos := by
  have htop : topSmall d a hpos ⊆ firstVals d σ a := by
    intro x hx
    by_contra hxL
    have hun : x ∈ firstVals d σ a ∪ secondVals d σ a := by
      rw [(vals_disjoint_union d σ a).2]
      exact Finset.mem_univ x
    have hxR : x ∈ secondVals d σ a := by
      rcases Finset.mem_union.mp hun with hx' | hx'
      · exact absurd hx' hxL
      · exact hx'
    have hxle : x ≤ σ a.succ := by
      rw [← secondVals_max d σ a ha]
      exact Finset.le_max' _ _ hxR
    have hxprev : x < σ (prevPos d a hpos) := lt_of_le_of_lt hxle hfail
    have hxge : d + 2 - a.val ≤ x.val := by
      simp only [topSmall, Finset.mem_Ici] at hx
      change d + 2 - a.val ≤ x.val at hx
      exact hx
    have hp := mpe_prev_le_threshold d σ a ha hpos
    exact (by omega)
  simp only [exclA, Finset.mem_filter, Finset.mem_powersetCard]
  exact ⟨⟨Finset.subset_univ _, firstVals_card d σ a⟩, htop⟩

private theorem mpe_threshold_le_next_succ (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a})
    (hlt : a.val < d) :
    d - a.val ≤ (σ (nextPos d a hlt)).val + 1 := by
  let s := Finset.image
    (fun i : Fin (d - a.val) => σ (block2Pos d a i.succ)) Finset.univ
  have hcard : s.card = d - a.val := by
    rw [Finset.card_image_of_injective]
    · simp only [Finset.card_univ, Fintype.card_fin]
    · intro i j hij
      apply Fin.ext
      have hv := congrArg Fin.val (block2Pos_inj d a (σ.injective hij))
      simp only [Fin.val_succ] at hv
      omega
  have hsub : s ⊆ Finset.Iic (σ (nextPos d a hlt)) := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    simp only [Finset.mem_Iic]
    have hle : (⟨1, by omega⟩ : Fin ((d - a.val) + 1)) ≤ i.succ := by
      change 1 ≤ i.val + 1
      omega
    rw [nextPos_eq_block2 d a hlt]
    rcases lt_or_eq_of_le hle with hlt' | heq
    · exact le_of_lt (block2_anti d σ a ha hlt')
    · rw [heq]
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  simpa only [Fin.card_Iic] using hle

private theorem mpe_mem_exclB_of_right_failure (d : ℕ)
    (σ : Equiv.Perm (Fin (d + 2))) (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a})
    (hlt : a.val < d)
    (hfail : σ (nextPos d a hlt) < σ a.castSucc) :
    firstVals d σ a ∈ exclB d a := by
  have htail := mpe_threshold_le_next_succ d σ a ha hlt
  have hmin : d - a.val ≤ (σ a.castSucc).val := by
    omega
  have hsub : firstVals d σ a ⊆ topLarge d a := by
    intro x hx
    have hminle : σ a.castSucc ≤ x := by
      rw [← firstVals_min d σ a ha]
      exact Finset.min'_le _ _ hx
    simp only [topLarge, Finset.mem_Ici]
    change d - a.val ≤ x.val
    omega
  simp only [exclB, Finset.mem_filter, Finset.mem_powersetCard]
  exact ⟨⟨Finset.subset_univ _, firstVals_card d σ a⟩, hsub⟩

private def mpeGood (d : ℕ) (σ : Equiv.Perm (Fin (d + 2))) : Prop :=
  (Finset.univ.filter fun i : Fin (d + 1) =>
    σ i.castSucc > σ i.succ).card = d ∧
  ∀ j : Fin (d + 2),
    (Finset.univ.filter fun i : Fin d =>
      σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)).card < d

private theorem mpeGood_forward (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (hgood : mpeGood d σ) :
    ∃ (a : Fin (d + 1)) (hpos : 0 < a.val), a.val < d ∧
      (Finset.univ.filter fun i : Fin (d + 1) =>
        σ i.castSucc < σ i.succ) = {a} ∧
      firstVals d σ a ∉ exclA d a hpos ∪ exclB d a := by
  obtain ⟨hdesc, hmin⟩ := hgood
  obtain ⟨a, ha⟩ := ascent_singleton_of_descent d σ hdesc
  have hpos : 0 < a.val := by
    by_contra h
    have hav : a.val = 0 := by omega
    have heq := end_first_not_minimal d σ a ha hav
    have hlt := hmin 0
    rw [heq] at hlt
    omega
  have hlt : a.val < d := by
    by_contra h
    have hav : a.val = d := by
      have hais := a.isLt
      omega
    have heq := end_last_not_minimal d σ a ha hav
    have hbad := hmin (Fin.last (d + 1))
    rw [heq] at hbad
    omega
  refine ⟨a, hpos, hlt, ha, ?_⟩
  simp only [Finset.mem_union, not_or]
  constructor
  · intro hA
    have hfail := left_failure_of_memA d σ a ha hpos hlt hA
    have hbridge := left_bridge_ascent_of_minimal d σ a ha hpos hmin
    exact lt_asymm hbridge hfail
  · intro hB
    have hfail := right_failure_of_memB d σ a ha hpos hlt hB
    have hbridge := right_bridge_ascent_of_minimal d σ a ha hlt hmin
    exact lt_asymm hbridge hfail

private theorem mpeGood_backward (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1)) (hpos : 0 < a.val) (hlt : a.val < d)
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a})
    (hallowed : firstVals d σ a ∉ exclA d a hpos ∪ exclB d a) :
    mpeGood d σ := by
  simp only [Finset.mem_union, not_or] at hallowed
  have hleft : σ (prevPos d a hpos) < σ a.succ := by
    have hposne : prevPos d a hpos ≠ a.succ := by
      intro heq
      have hv := congrArg Fin.val heq
      simp only [prevPos_val, Fin.val_succ] at hv
      omega
    have hne : σ (prevPos d a hpos) ≠ σ a.succ :=
      fun heq => hposne (σ.injective heq)
    rcases lt_or_gt_of_ne hne with hbridge | hfail
    · exact hbridge
    · exact absurd (mpe_mem_exclA_of_left_failure d σ a ha hpos hfail) hallowed.1
  have hright : σ a.castSucc < σ (nextPos d a hlt) := by
    have hposne : a.castSucc ≠ nextPos d a hlt := by
      intro heq
      have hv := congrArg Fin.val heq
      simp only [Fin.val_castSucc, nextPos_val] at hv
      omega
    have hne : σ a.castSucc ≠ σ (nextPos d a hlt) :=
      fun heq => hposne (σ.injective heq)
    rcases lt_or_gt_of_ne hne with hbridge | hfail
    · exact hbridge
    · exact absurd (mpe_mem_exclB_of_right_failure d σ a ha hlt hfail) hallowed.2
  have hasc : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ).card = 1 := by
    rw [ha]
    simp
  have hadd := descent_add_ascent d σ
  have hdesc : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc > σ i.succ).card = d := by omega
  exact ⟨hdesc, minimal_of_bridges d σ a ha hpos hlt hleft hright⟩

private theorem mpe_secondVals_eq_compl (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1)) :
    secondVals d σ a = (firstVals d σ a)ᶜ := by
  have hpartition := vals_disjoint_union d σ a
  ext x
  simp only [Finset.mem_compl]
  constructor
  · intro hxR hxL
    exact Finset.disjoint_left.mp hpartition.1 hxL hxR
  · intro hxL
    have hx : x ∈ firstVals d σ a ∪ secondVals d σ a := by
      rw [hpartition.2]
      exact Finset.mem_univ x
    rcases Finset.mem_union.mp hx with hx' | hx'
    · exact absurd hx' hxL
    · exact hx'

private theorem mpe_block1_eq (d : ℕ) (σ τ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1))
    (haσ : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a})
    (haτ : (Finset.univ.filter fun i : Fin (d + 1) =>
      τ i.castSucc < τ i.succ) = {a})
    (hvals : firstVals d σ a = firstVals d τ a) :
    (fun i : Fin (a.val + 1) => σ (block1Pos d a i)) =
      fun i => τ (block1Pos d a i) := by
  have hσ : (fun i : Fin (a.val + 1) =>
      σ (block1Pos d a (Fin.rev i))) =
      (firstVals d σ a).orderEmbOfFin (firstVals_card d σ a) := by
    apply Finset.orderEmbOfFin_unique
    · intro i
      simp only [firstVals, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨Fin.rev i, rfl⟩
    · exact (block1_anti d σ a haσ).comp Fin.rev_strictAnti
  have hτ : (fun i : Fin (a.val + 1) =>
      τ (block1Pos d a (Fin.rev i))) =
      (firstVals d σ a).orderEmbOfFin (firstVals_card d σ a) := by
    apply Finset.orderEmbOfFin_unique
    · intro i
      rw [hvals]
      simp only [firstVals, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨Fin.rev i, rfl⟩
    · exact (block1_anti d τ a haτ).comp Fin.rev_strictAnti
  funext i
  have hi := congrFun (hσ.trans hτ.symm) (Fin.rev i)
  simpa only [Fin.rev_rev] using hi

private theorem mpe_block2_eq (d : ℕ) (σ τ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1))
    (haσ : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a})
    (haτ : (Finset.univ.filter fun i : Fin (d + 1) =>
      τ i.castSucc < τ i.succ) = {a})
    (hvals : firstVals d σ a = firstVals d τ a) :
    (fun i : Fin ((d - a.val) + 1) => σ (block2Pos d a i)) =
      fun i => τ (block2Pos d a i) := by
  have hvals2 : secondVals d σ a = secondVals d τ a := by
    rw [mpe_secondVals_eq_compl d σ a, mpe_secondVals_eq_compl d τ a, hvals]
  have hσ : (fun i : Fin ((d - a.val) + 1) =>
      σ (block2Pos d a (Fin.rev i))) =
      (secondVals d σ a).orderEmbOfFin (secondVals_card d σ a) := by
    apply Finset.orderEmbOfFin_unique
    · intro i
      simp only [secondVals, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨Fin.rev i, rfl⟩
    · exact (block2_anti d σ a haσ).comp Fin.rev_strictAnti
  have hτ : (fun i : Fin ((d - a.val) + 1) =>
      τ (block2Pos d a (Fin.rev i))) =
      (secondVals d σ a).orderEmbOfFin (secondVals_card d σ a) := by
    apply Finset.orderEmbOfFin_unique
    · intro i
      rw [hvals2]
      simp only [secondVals, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨Fin.rev i, rfl⟩
    · exact (block2_anti d τ a haτ).comp Fin.rev_strictAnti
  funext i
  have hi := congrFun (hσ.trans hτ.symm) (Fin.rev i)
  simpa only [Fin.rev_rev] using hi

private theorem mpe_reconstruct_injective (d : ℕ)
    (σ τ : Equiv.Perm (Fin (d + 2))) (a : Fin (d + 1))
    (haσ : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a})
    (haτ : (Finset.univ.filter fun i : Fin (d + 1) =>
      τ i.castSucc < τ i.succ) = {a})
    (hvals : firstVals d σ a = firstVals d τ a) : σ = τ := by
  have hblock1 := mpe_block1_eq d σ τ a haσ haτ hvals
  have hblock2 := mpe_block2_eq d σ τ a haσ haτ hvals
  apply Equiv.ext
  intro p
  by_cases hp : p.val ≤ a.val
  · let i : Fin (a.val + 1) := ⟨p.val, by omega⟩
    have heq : block1Pos d a i = p := by
      apply Fin.ext
      simp only [block1Pos_val]
      rfl
    rw [← heq]
    exact congrFun hblock1 i
  · have hle : a.val + 1 ≤ p.val := by omega
    let i : Fin ((d - a.val) + 1) :=
      ⟨p.val - (a.val + 1), by
        have hp' := p.isLt
        have ha' := a.isLt
        omega⟩
    have heq : block2Pos d a i = p := by
      apply Fin.ext
      simp only [block2Pos_val]
      change a.val + 1 + (p.val - (a.val + 1)) = p.val
      omega
    rw [← heq]
    exact congrFun hblock2 i

private theorem mpe_compl_card (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1) :
    Lᶜ.card = (d - a.val) + 1 := by
  rw [Finset.card_compl, hL]
  simp only [Fintype.card_fin]
  have ha := a.isLt
  omega

private def mpeFirstIndex (d : ℕ) (a : Fin (d + 1)) (p : Fin (d + 2))
    (h : p.val ≤ a.val) : Fin (a.val + 1) :=
  ⟨p.val, by omega⟩

private theorem mpeFirstIndex_val (d : ℕ) (a : Fin (d + 1)) (p : Fin (d + 2))
    (h : p.val ≤ a.val) : (mpeFirstIndex d a p h).val = p.val := rfl

private def mpeSecondIndex (d : ℕ) (a : Fin (d + 1)) (p : Fin (d + 2))
    (h : ¬p.val ≤ a.val) : Fin ((d - a.val) + 1) :=
  ⟨p.val - (a.val + 1), by
    have hp := p.isLt
    have ha := a.isLt
    omega⟩

private theorem mpeSecondIndex_val (d : ℕ) (a : Fin (d + 1)) (p : Fin (d + 2))
    (h : ¬p.val ≤ a.val) :
    (mpeSecondIndex d a p h).val = p.val - (a.val + 1) := rfl

private noncomputable def mpeConstructFun (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1) :
    Fin (d + 2) → Fin (d + 2) := fun p =>
  if h : p.val ≤ a.val then
    L.orderEmbOfFin hL (Fin.rev (mpeFirstIndex d a p h))
  else
    Lᶜ.orderEmbOfFin (mpe_compl_card d a L hL)
      (Fin.rev (mpeSecondIndex d a p h))

private theorem mpeConstructFun_mem_left (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1)
    (p : Fin (d + 2)) (hp : p.val ≤ a.val) :
    mpeConstructFun d a L hL p ∈ L := by
  simp only [mpeConstructFun, hp, ↓reduceDIte]
  exact Finset.orderEmbOfFin_mem L hL _

private theorem mpeConstructFun_not_mem_right (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1)
    (p : Fin (d + 2)) (hp : ¬p.val ≤ a.val) :
    mpeConstructFun d a L hL p ∉ L := by
  simp only [mpeConstructFun, hp, ↓reduceDIte]
  exact Finset.mem_compl.mp
    (Finset.orderEmbOfFin_mem Lᶜ (mpe_compl_card d a L hL) _)

private theorem mpeConstructFun_injective (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1) :
    Function.Injective (mpeConstructFun d a L hL) := by
  intro p q heq
  by_cases hp : p.val ≤ a.val
  · by_cases hq : q.val ≤ a.val
    · have heq' := heq
      simp only [mpeConstructFun, hp, hq, ↓reduceDIte] at heq'
      have hi := (L.orderEmbOfFin hL).injective heq'
      have hirev := Fin.rev_injective hi
      apply Fin.ext
      have hv := congrArg Fin.val hirev
      simpa only [mpeFirstIndex_val] using hv
    · have hpL := mpeConstructFun_mem_left d a L hL p hp
      have hqL := mpeConstructFun_not_mem_right d a L hL q hq
      exact absurd (heq ▸ hpL) hqL
  · by_cases hq : q.val ≤ a.val
    · have hpL := mpeConstructFun_not_mem_right d a L hL p hp
      have hqL := mpeConstructFun_mem_left d a L hL q hq
      exact absurd (heq.symm ▸ hqL) hpL
    · have heq' := heq
      simp only [mpeConstructFun, hp, hq, ↓reduceDIte] at heq'
      have hi := (Lᶜ.orderEmbOfFin (mpe_compl_card d a L hL)).injective heq'
      have hirev := Fin.rev_injective hi
      apply Fin.ext
      have hv := congrArg Fin.val hirev
      simp only [mpeSecondIndex_val] at hv
      omega

private noncomputable def mpeConstruct (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1) :
    Equiv.Perm (Fin (d + 2)) :=
  Equiv.ofBijective (mpeConstructFun d a L hL)
    (mpeConstructFun_injective d a L hL).bijective_of_finite

private theorem mpeConstruct_apply (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1) (p : Fin (d + 2)) :
    mpeConstruct d a L hL p = mpeConstructFun d a L hL p := rfl

private theorem mpeConstruct_block1 (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1)
    (i : Fin (a.val + 1)) :
    mpeConstruct d a L hL (block1Pos d a i) =
      L.orderEmbOfFin hL (Fin.rev i) := by
  rw [mpeConstruct_apply]
  have hi : (block1Pos d a i).val ≤ a.val := by
    simp only [block1Pos_val]
    omega
  simp only [mpeConstructFun, hi, ↓reduceDIte]
  have hidx : mpeFirstIndex d a (block1Pos d a i) hi = i := by
    apply Fin.ext
    simp only [mpeFirstIndex_val, block1Pos_val]
  rw [hidx]

private theorem mpeConstruct_block2 (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1)
    (i : Fin ((d - a.val) + 1)) :
    mpeConstruct d a L hL (block2Pos d a i) =
      Lᶜ.orderEmbOfFin (mpe_compl_card d a L hL) (Fin.rev i) := by
  rw [mpeConstruct_apply]
  have hi : ¬(block2Pos d a i).val ≤ a.val := by
    simp only [block2Pos_val]
    omega
  simp only [mpeConstructFun, hi, ↓reduceDIte]
  have hidx : mpeSecondIndex d a (block2Pos d a i) hi = i := by
    apply Fin.ext
    simp only [mpeSecondIndex_val, block2Pos_val]
    omega
  rw [hidx]

private theorem mpeConstruct_block1_anti (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1) :
    StrictAnti (fun i : Fin (a.val + 1) =>
      mpeConstruct d a L hL (block1Pos d a i)) := by
  intro i j hij
  change mpeConstruct d a L hL (block1Pos d a j) <
    mpeConstruct d a L hL (block1Pos d a i)
  rw [mpeConstruct_block1, mpeConstruct_block1]
  exact (L.orderEmbOfFin hL).strictMono (Fin.rev_strictAnti hij)

private theorem mpeConstruct_block2_anti (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1) :
    StrictAnti (fun i : Fin ((d - a.val) + 1) =>
      mpeConstruct d a L hL (block2Pos d a i)) := by
  intro i j hij
  change mpeConstruct d a L hL (block2Pos d a j) <
    mpeConstruct d a L hL (block2Pos d a i)
  rw [mpeConstruct_block2, mpeConstruct_block2]
  exact (Lᶜ.orderEmbOfFin (mpe_compl_card d a L hL)).strictMono
    (Fin.rev_strictAnti hij)

private theorem mpeConstruct_firstVals (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1) :
    firstVals d (mpeConstruct d a L hL) a = L := by
  ext y
  simp only [firstVals, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    rw [mpeConstruct_block1]
    exact Finset.orderEmbOfFin_mem L hL _
  · intro hy
    have hy' : y ∈ Finset.image (L.orderEmbOfFin hL) Finset.univ := by
      rw [Finset.image_orderEmbOfFin_univ]
      exact hy
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hy'
    refine ⟨Fin.rev i, ?_⟩
    rw [mpeConstruct_block1, Fin.rev_rev]
    exact hi

private theorem mpeConstruct_left_endpoint (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1) :
    mpeConstruct d a L hL a.castSucc =
      L.orderEmbOfFin hL 0 := by
  have heq : a.castSucc = block1Pos d a (Fin.last a.val) := by
    apply Fin.ext
    simp only [Fin.val_castSucc, block1Pos_val, Fin.val_last]
  rw [heq, mpeConstruct_block1, Fin.rev_last]

private theorem mpeConstruct_right_endpoint (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1) :
    mpeConstruct d a L hL a.succ =
      Lᶜ.orderEmbOfFin (mpe_compl_card d a L hL) (Fin.last (d - a.val)) := by
  have heq : a.succ = block2Pos d a 0 := by
    apply Fin.ext
    simp only [Fin.val_succ, block2Pos_val, Fin.val_zero, add_zero]
  rw [heq, mpeConstruct_block2, Fin.rev_zero]

private theorem mpeConstruct_memB_of_gap_descent (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1)
    (hdesc : mpeConstruct d a L hL a.succ < mpeConstruct d a L hL a.castSucc) :
    L ∈ exclB d a := by
  have hright : ∀ y ∈ Lᶜ, y ≤ mpeConstruct d a L hL a.succ := by
    intro y hy
    have hy' : y ∈ Finset.image
        (Lᶜ.orderEmbOfFin (mpe_compl_card d a L hL)) Finset.univ := by
      rw [Finset.image_orderEmbOfFin_univ]
      exact hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy'
    rw [mpeConstruct_right_endpoint]
    exact (Lᶜ.orderEmbOfFin (mpe_compl_card d a L hL)).monotone (Fin.le_last i)
  have hsubC : Lᶜ ⊆ Finset.Iic (mpeConstruct d a L hL a.succ) := by
    intro y hy
    exact Finset.mem_Iic.mpr (hright y hy)
  have hcard := Finset.card_le_card hsubC
  rw [mpe_compl_card d a L hL] at hcard
  simp only [Fin.card_Iic] at hcard
  have hsubL : L ⊆ topLarge d a := by
    intro x hx
    have hx' : x ∈ Finset.image (L.orderEmbOfFin hL) Finset.univ := by
      rw [Finset.image_orderEmbOfFin_univ]
      exact hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx'
    have hleft : mpeConstruct d a L hL a.castSucc ≤ L.orderEmbOfFin hL i := by
      rw [mpeConstruct_left_endpoint]
      exact (L.orderEmbOfFin hL).monotone (Fin.zero_le i)
    simp only [topLarge, Finset.mem_Ici]
    change d - a.val ≤ (L.orderEmbOfFin hL i).val
    omega
  simp only [exclB, Finset.mem_filter, Finset.mem_powersetCard]
  exact ⟨⟨Finset.subset_univ _, hL⟩, hsubL⟩

private theorem mpeConstruct_gap_ascent (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1)
    (hB : L ∉ exclB d a) :
    mpeConstruct d a L hL a.castSucc < mpeConstruct d a L hL a.succ := by
  have hposne : a.castSucc ≠ a.succ := by
    intro heq
    have hv := congrArg Fin.val heq
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  have hne : mpeConstruct d a L hL a.castSucc ≠
      mpeConstruct d a L hL a.succ :=
    fun heq => hposne ((mpeConstruct d a L hL).injective heq)
  rcases lt_or_gt_of_ne hne with hasc | hdesc
  · exact hasc
  · exact absurd (mpeConstruct_memB_of_gap_descent d a L hL hdesc) hB

private theorem mpeConstruct_descent_of_ne (d : ℕ) (a k : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1) (hk : k ≠ a) :
    mpeConstruct d a L hL k.succ < mpeConstruct d a L hL k.castSucc := by
  have hvne : k.val ≠ a.val := fun heq => hk (Fin.ext heq)
  rcases lt_or_gt_of_ne hvne with hlt | hgt
  · let i : Fin a.val := ⟨k.val, hlt⟩
    have hi : i.castSucc < i.succ := by
      change i.val < i.val + 1
      omega
    have hdesc := mpeConstruct_block1_anti d a L hL hi
    have heq1 : block1Pos d a i.castSucc = k.castSucc := by
      apply Fin.ext
      simp only [block1Pos_val, Fin.val_castSucc]
      rfl
    have heq2 : block1Pos d a i.succ = k.succ := by
      apply Fin.ext
      simp only [block1Pos_val, Fin.val_succ]
      rfl
    change mpeConstruct d a L hL (block1Pos d a i.succ) <
      mpeConstruct d a L hL (block1Pos d a i.castSucc) at hdesc
    rw [heq1, heq2] at hdesc
    exact hdesc
  · have hklt := k.isLt
    have ha := a.isLt
    let i : Fin (d - a.val) := ⟨k.val - (a.val + 1), by omega⟩
    have hi : i.castSucc < i.succ := by
      change i.val < i.val + 1
      omega
    have hdesc := mpeConstruct_block2_anti d a L hL hi
    have heq1 : block2Pos d a i.castSucc = k.castSucc := by
      apply Fin.ext
      simp only [block2Pos_val, Fin.val_castSucc]
      change a.val + 1 + (k.val - (a.val + 1)) = k.val
      omega
    have heq2 : block2Pos d a i.succ = k.succ := by
      apply Fin.ext
      simp only [block2Pos_val, Fin.val_succ]
      change a.val + 1 + (k.val - (a.val + 1) + 1) = k.val + 1
      omega
    change mpeConstruct d a L hL (block2Pos d a i.succ) <
      mpeConstruct d a L hL (block2Pos d a i.castSucc) at hdesc
    rw [heq1, heq2] at hdesc
    exact hdesc

private theorem mpeConstruct_ascent_singleton (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1)
    (hB : L ∉ exclB d a) :
    (Finset.univ.filter fun i : Fin (d + 1) =>
      mpeConstruct d a L hL i.castSucc < mpeConstruct d a L hL i.succ) = {a} := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hasc
    by_contra hk
    have hdesc := mpeConstruct_descent_of_ne d a k L hL hk
    exact (lt_asymm hasc hdesc)
  · intro hk
    subst k
    exact mpeConstruct_gap_ascent d a L hL hB

private noncomputable def mpeAscentPos (d : ℕ) (σ : Equiv.Perm (Fin (d + 2))) :
    Fin (d + 1) := by
  classical
  exact if h : mpeGood d σ then (mpeGood_forward d σ h).choose else 0

private theorem mpeAscentPos_spec (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (hgood : mpeGood d σ) :
    ∃ hpos : 0 < (mpeAscentPos d σ).val,
      (mpeAscentPos d σ).val < d ∧
      (Finset.univ.filter fun i : Fin (d + 1) =>
        σ i.castSucc < σ i.succ) = {mpeAscentPos d σ} ∧
      firstVals d σ (mpeAscentPos d σ) ∉
        exclA d (mpeAscentPos d σ) hpos ∪ exclB d (mpeAscentPos d σ) := by
  unfold mpeAscentPos
  simp only [hgood, ↓reduceDIte]
  exact (mpeGood_forward d σ hgood).choose_spec

private noncomputable def mpePerms (d : ℕ) : Finset (Equiv.Perm (Fin (d + 2))) := by
  classical
  exact Finset.univ.filter (mpeGood d)

private def mpePositions (d : ℕ) : Finset (Fin (d + 1)) :=
  Finset.univ.filter fun a => 0 < a.val ∧ a.val < d

private def mpeAllowed (d : ℕ) (a : Fin (d + 1)) (hpos : 0 < a.val) :
    Finset (Finset (Fin (d + 2))) :=
  Finset.powersetCard (a.val + 1) Finset.univ \ (exclA d a hpos ∪ exclB d a)

private noncomputable def mpeFiber (d : ℕ) (a : Fin (d + 1)) :
    Finset (Equiv.Perm (Fin (d + 2))) :=
  (mpePerms d).filter fun σ => mpeAscentPos d σ = a

private theorem mpePerms_mem (d : ℕ) (σ : Equiv.Perm (Fin (d + 2))) :
    σ ∈ mpePerms d ↔ mpeGood d σ := by
  classical
  simp only [mpePerms, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem mpePositions_mem (d : ℕ) (a : Fin (d + 1)) :
    a ∈ mpePositions d ↔ 0 < a.val ∧ a.val < d := by
  simp only [mpePositions, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem mpeAllowed_mem (d : ℕ) (a : Fin (d + 1)) (hpos : 0 < a.val)
    (L : Finset (Fin (d + 2))) :
    L ∈ mpeAllowed d a hpos ↔
      L.card = a.val + 1 ∧ L ∉ exclA d a hpos ∪ exclB d a := by
  simp only [mpeAllowed, Finset.mem_sdiff, Finset.mem_powersetCard,
    Finset.subset_univ, true_and]

private theorem mpeFiber_ascent (d : ℕ) (a : Fin (d + 1))
    (σ : Equiv.Perm (Fin (d + 2))) (hσ : σ ∈ mpeFiber d a) :
    mpeGood d σ ∧
      (Finset.univ.filter fun i : Fin (d + 1) =>
        σ i.castSucc < σ i.succ) = {a} := by
  have hfiber := Finset.mem_filter.mp hσ
  have hgood := (mpePerms_mem d σ).mp hfiber.1
  obtain ⟨_, _, hasc, _⟩ := mpeAscentPos_spec d σ hgood
  rw [hfiber.2] at hasc
  exact ⟨hgood, hasc⟩

private theorem mpeFiber_firstVals_mem (d : ℕ) (a : Fin (d + 1))
    (hpos : 0 < a.val) (σ : Equiv.Perm (Fin (d + 2))) (hσ : σ ∈ mpeFiber d a) :
    firstVals d σ a ∈ mpeAllowed d a hpos := by
  have hfiber := Finset.mem_filter.mp hσ
  have hgood := (mpePerms_mem d σ).mp hfiber.1
  have haeq := hfiber.2
  subst a
  obtain ⟨_, _, _, hallowed⟩ := mpeAscentPos_spec d σ hgood
  apply (mpeAllowed_mem d (mpeAscentPos d σ) hpos _).mpr
  exact ⟨firstVals_card d σ (mpeAscentPos d σ), hallowed⟩

private theorem mpeConstruct_mem_fiber (d : ℕ) (a : Fin (d + 1))
    (hpos : 0 < a.val) (hlt : a.val < d) (L : Finset (Fin (d + 2)))
    (hL : L.card = a.val + 1)
    (hallowed : L ∉ exclA d a hpos ∪ exclB d a) :
    mpeConstruct d a L hL ∈ mpeFiber d a := by
  have hB : L ∉ exclB d a := by
    intro hmem
    exact hallowed (Finset.mem_union.mpr (Or.inr hmem))
  have hasc := mpeConstruct_ascent_singleton d a L hL hB
  have hfirst := mpeConstruct_firstVals d a L hL
  have hallowed' : firstVals d (mpeConstruct d a L hL) a ∉
      exclA d a hpos ∪ exclB d a := by
    rw [hfirst]
    exact hallowed
  have hgood := mpeGood_backward d (mpeConstruct d a L hL) a hpos hlt hasc hallowed'
  have hposEq : mpeAscentPos d (mpeConstruct d a L hL) = a := by
    obtain ⟨_, _, hasc', _⟩ := mpeAscentPos_spec d (mpeConstruct d a L hL) hgood
    have hmem : mpeAscentPos d (mpeConstruct d a L hL) ∈ ({a} : Finset _) := by
      rw [← hasc, hasc']
      exact Finset.mem_singleton_self _
    exact Finset.mem_singleton.mp hmem
  apply Finset.mem_filter.mpr
  exact ⟨(mpePerms_mem d _).mpr hgood, hposEq⟩

private theorem mpeFiber_card_allowed (d : ℕ) (a : Fin (d + 1))
    (hpos : 0 < a.val) (hlt : a.val < d) :
    (mpeFiber d a).card = (mpeAllowed d a hpos).card := by
  classical
  apply Finset.card_bij
    (fun σ _ => firstVals d σ a)
    (fun σ hσ => mpeFiber_firstVals_mem d a hpos σ hσ)
  · intro σ₁ hσ₁ σ₂ hσ₂ heq
    have ha₁ := (mpeFiber_ascent d a σ₁ hσ₁).2
    have ha₂ := (mpeFiber_ascent d a σ₂ hσ₂).2
    exact mpe_reconstruct_injective d σ₁ σ₂ a ha₁ ha₂ heq
  · intro L hmem
    obtain ⟨hL, hallowed⟩ := (mpeAllowed_mem d a hpos L).mp hmem
    refine ⟨mpeConstruct d a L hL,
      mpeConstruct_mem_fiber d a hpos hlt L hL hallowed, ?_⟩
    exact mpeConstruct_firstVals d a L hL

private def mpeAllowedAt (d : ℕ) (a : Fin (d + 1)) :
    Finset (Finset (Fin (d + 2))) :=
  if hpos : 0 < a.val then mpeAllowed d a hpos else ∅

private theorem mpeAllowedAt_eq (d : ℕ) (a : Fin (d + 1)) (hpos : 0 < a.val) :
    mpeAllowedAt d a = mpeAllowed d a hpos := by
  simp only [mpeAllowedAt, hpos, ↓reduceDIte]

private theorem mpePerms_card_sum (d : ℕ) :
    (mpePerms d).card =
      ∑ a ∈ mpePositions d, (mpeAllowedAt d a).card := by
  classical
  have hmaps : (↑(mpePerms d) : Set (Equiv.Perm (Fin (d + 2)))).MapsTo
      (mpeAscentPos d) (mpePositions d) := by
    intro σ hσ
    have hgood := (mpePerms_mem d σ).mp hσ
    obtain ⟨hpos, hlt, _, _⟩ := mpeAscentPos_spec d σ hgood
    exact (mpePositions_mem d (mpeAscentPos d σ)).mpr ⟨hpos, hlt⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro a ha
  obtain ⟨hpos, hlt⟩ := (mpePositions_mem d a).mp ha
  change (mpeFiber d a).card = (mpeAllowedAt d a).card
  rw [mpeAllowedAt_eq d a hpos]
  exact mpeFiber_card_allowed d a hpos hlt

private theorem mpe_excl_union_subset (d : ℕ) (a : Fin (d + 1))
    (hpos : 0 < a.val) :
    exclA d a hpos ∪ exclB d a ⊆
      Finset.powersetCard (a.val + 1) Finset.univ := by
  intro L hL
  rcases Finset.mem_union.mp hL with hA | hB
  · exact (Finset.mem_filter.mp hA).1
  · exact (Finset.mem_filter.mp hB).1

private theorem mpeAllowed_card (d : ℕ) (a : Fin (d + 1)) (hpos : 0 < a.val) :
    (mpeAllowed d a hpos).card = Nat.choose (d + 2) (a.val + 1) - (d + 2) := by
  rw [mpeAllowed, Finset.card_sdiff_of_subset (mpe_excl_union_subset d a hpos)]
  rw [Finset.card_powersetCard, exclUnion_card d a hpos]
  simp only [Finset.card_univ, Fintype.card_fin]

private theorem mpePositions_eq_Ioo (d : ℕ) :
    mpePositions d = Finset.Ioo (0 : Fin (d + 1)) (Fin.last d) := by
  ext a
  simp only [mpePositions_mem, Finset.mem_Ioo]
  change (0 < a.val ∧ a.val < d) ↔ 0 < a.val ∧ a.val < d
  rfl

private theorem mpePositions_card (d : ℕ) : (mpePositions d).card = d - 1 := by
  rw [mpePositions_eq_Ioo]
  simp only [Fin.card_Ioo, Fin.val_last, Fin.val_zero, Nat.sub_zero]

private theorem mpeAllowed_card_add (d : ℕ) (a : Fin (d + 1))
    (hpos : 0 < a.val) :
    (mpeAllowed d a hpos).card + (d + 2) = Nat.choose (d + 2) (a.val + 1) := by
  have hle := Finset.card_le_card (mpe_excl_union_subset d a hpos)
  rw [exclUnion_card d a hpos, Finset.card_powersetCard] at hle
  simp only [Finset.card_univ, Fintype.card_fin] at hle
  have hcard := mpeAllowed_card d a hpos
  omega

private theorem mpe_choose_sum_all (d : ℕ) :
    (∑ a : Fin (d + 1), Nat.choose (d + 2) (a.val + 1)) + 2 = 2 ^ (d + 2) := by
  have hsum := Nat.sum_range_choose (d + 2)
  rw [Finset.sum_range] at hsum
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc] at hsum
  simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last,
    Nat.choose_zero_right, Nat.choose_self] at hsum
  omega

private theorem mpe_univ_eq_insert_positions (d : ℕ) :
    (Finset.univ : Finset (Fin (d + 1))) =
      insert 0 (insert (Fin.last d) (mpePositions d)) := by
  ext a
  simp only [Finset.mem_univ, Finset.mem_insert, mpePositions_mem, true_iff]
  by_cases hzero : a.val = 0
  · exact Or.inl (Fin.ext hzero)
  · by_cases hlast : a.val = d
    · exact Or.inr (Or.inl (Fin.ext hlast))
    · exact Or.inr (Or.inr ⟨by omega, by have ha := a.isLt; omega⟩)

private theorem mpe_choose_sum_positions (d : ℕ) (hd : 2 ≤ d) :
    (∑ a ∈ mpePositions d, Nat.choose (d + 2) (a.val + 1)) +
      2 * (d + 2) + 2 = 2 ^ (d + 2) := by
  have hzero : (0 : Fin (d + 1)) ∉ insert (Fin.last d) (mpePositions d) := by
    simp only [Finset.mem_insert, not_or]
    constructor
    · intro heq
      have hv := congrArg Fin.val heq
      simp only [Fin.val_zero, Fin.val_last] at hv
      omega
    · intro hmem
      have hbounds := (mpePositions_mem d 0).mp hmem
      simp only [Fin.val_zero] at hbounds
      omega
  have hlast : Fin.last d ∉ mpePositions d := by
    intro hmem
    have hbounds := (mpePositions_mem d (Fin.last d)).mp hmem
    simp only [Fin.val_last] at hbounds
    omega
  have hsum := mpe_choose_sum_all d
  change (∑ a ∈ (Finset.univ : Finset (Fin (d + 1))),
    Nat.choose (d + 2) (a.val + 1)) + 2 = 2 ^ (d + 2) at hsum
  rw [mpe_univ_eq_insert_positions d, Finset.sum_insert hzero,
    Finset.sum_insert hlast] at hsum
  simp only [Fin.val_zero, Fin.val_last, zero_add, Nat.choose_one_right,
    Nat.choose_succ_self_right] at hsum
  omega

private theorem mpePerms_card_add (d : ℕ) (hd : 2 ≤ d) :
    (mpePerms d).card + (d + 1) * (d + 2) + 2 = 2 ^ (d + 2) := by
  have hterms :
      (mpePositions d).sum (fun a => (mpeAllowedAt d a).card + (d + 2)) =
        (mpePositions d).sum (fun a => Nat.choose (d + 2) (a.val + 1)) := by
    refine Finset.sum_congr rfl ?_
    intro a ha
    obtain ⟨hpos, _⟩ := (mpePositions_mem d a).mp ha
    rw [mpeAllowedAt_eq d a hpos]
    exact mpeAllowed_card_add d a hpos
  rw [Finset.sum_add_distrib] at hterms
  simp only [Finset.sum_const, nsmul_eq_mul] at hterms
  rw [mpePositions_card d] at hterms
  have hterms' :
      (∑ a ∈ mpePositions d, (mpeAllowedAt d a).card) +
        (d - 1) * (d + 2) =
          ∑ a ∈ mpePositions d, Nat.choose (d + 2) (a.val + 1) := by
    simpa using hterms
  have hcard := mpePerms_card_sum d
  have hchoose := mpe_choose_sum_positions d hd
  have hd' : d + 1 = (d - 1) + 2 := by omega
  have hfactor : (d + 1) * (d + 2) =
      (d - 1) * (d + 2) + 2 * (d + 2) := by
    rw [hd', Nat.add_mul]
  rw [hcard, hfactor]
  calc
    _ = ((∑ a ∈ mpePositions d, (mpeAllowedAt d a).card) +
          (d - 1) * (d + 2)) + 2 * (d + 2) + 2 := by ac_rfl
    _ = (∑ a ∈ mpePositions d, Nat.choose (d + 2) (a.val + 1)) +
          2 * (d + 2) + 2 := by rw [hterms']
    _ = 2 ^ (d + 2) := hchoose

/--
**Minimal permutations of length two more than their number of descents.** For every natural
number $d$, the number of permutations $\sigma$ of $\{0, 1, \dots, d + 1\}$ such that $\sigma$ has
exactly $d$ descents (positions $0 \le i \le d$ with $\sigma(i) > \sigma(i + 1)$) and, for every
position $j$, deleting the entry at position $j$ leaves a sequence of $d + 1$ entries with fewer
than $d$ descents, equals $2^{d+2} - (d + 1)(d + 2) - 2$.

Proves `Wanted` entry `minimal_permutations_card`.

Source: Stefano Bilotta, Elisabetta Grazzini, and Elisa Pergola, "Enumeration of Two Particular Sets of Minimal Permutations", Journal of Integer Sequences 18 (2015), Article 15.10.2, Theorem `thm:enum`, lines 324-326, <https://cs.uwaterloo.ca/journals/JIS/VOL18/Grazzini/graz3.tex>.
-/
public theorem minimal_permutations_card (d : ℕ) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin (d + 2)) =>
      (Finset.univ.filter fun i : Fin (d + 1) =>
        σ i.castSucc > σ i.succ).card = d ∧
      ∀ j : Fin (d + 2),
        (Finset.univ.filter fun i : Fin d =>
          σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)).card < d).card =
      2 ^ (d + 2) - (d + 1) * (d + 2) - 2 := by
  classical
  have hset : (Finset.univ.filter fun σ : Equiv.Perm (Fin (d + 2)) =>
      (Finset.univ.filter fun i : Fin (d + 1) =>
        σ i.castSucc > σ i.succ).card = d ∧
      ∀ j : Fin (d + 2),
        (Finset.univ.filter fun i : Fin d =>
          σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)).card < d) =
      mpePerms d := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mpePerms_mem, mpeGood]
  rw [hset]
  by_cases hd : 2 ≤ d
  · have hadd := mpePerms_card_add d hd
    omega
  · have hsmall : d = 0 ∨ d = 1 := by omega
    rcases hsmall with rfl | rfl
    · have hcard := mpePerms_card_sum 0
      have hempty : mpePositions 0 = ∅ := Finset.card_eq_zero.mp (by
        rw [mpePositions_card])
      rw [hempty] at hcard
      simp only [Finset.sum_empty] at hcard
      norm_num [hcard]
    · have hcard := mpePerms_card_sum 1
      have hempty : mpePositions 1 = ∅ := Finset.card_eq_zero.mp (by
        rw [mpePositions_card])
      rw [hempty] at hcard
      simp only [Finset.sum_empty] at hcard
      norm_num [hcard]

end MetaMathlibExt
end
