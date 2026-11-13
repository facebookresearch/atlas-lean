/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

section
open scoped BigOperators

namespace MetaMathlibExt

private def oddC (n : ℕ) (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n =>
    if h : i.val + 1 < n then
      (i.val + 1) % 2 = 1 ∧ σ i > σ ⟨i.val + 1, h⟩
    else False).card

private def evenC (n : ℕ) (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n =>
    if h : i.val + 1 < n then
      (i.val + 1) % 2 = 0 ∧ σ i > σ ⟨i.val + 1, h⟩
    else False).card

private theorem eval_refined (n : ℕ) (p q : ℝ) :
    Polynomial.eval q (Polynomial.eval (Polynomial.C p)
      (∑ σ : Equiv.Perm (Fin n),
        Polynomial.C (Polynomial.X ^ evenC n σ) *
          Polynomial.X ^ oddC n σ)) =
    ∑ σ : Equiv.Perm (Fin n), p ^ oddC n σ * q ^ evenC n σ := by
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro σ _
  ring

private theorem range_count (n r : ℕ) (hr : r < 2) :
    ((Finset.range n).filter (fun k => (k + 1) % 2 = r ∧ k + 1 < n)).card
      = (n + r - 1) / 2 := by
  have himg : (Finset.range n).filter (fun k => (k + 1) % 2 = r ∧ k + 1 < n)
      = Finset.image (fun j => 2 * j + (1 - r)) (Finset.range ((n + r - 1) / 2)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · intro h
      obtain ⟨hrange, hpar, hbound⟩ := h
      exact ⟨k / 2, by omega, by omega⟩
    · intro h
      obtain ⟨j, hj, rfl⟩ := h
      exact ⟨by omega, by omega, by omega⟩
  rw [himg, Finset.card_image_of_injective _ (fun a b h => by omega), Finset.card_range]

private theorem fin_count (n r : ℕ) (hr : r < 2) :
    (Finset.univ.filter (fun i : Fin n => (i.val + 1) % 2 = r ∧ i.val + 1 < n)).card
      = (n + r - 1) / 2 := by
  have himg : Finset.image Fin.val
        (Finset.univ.filter (fun i : Fin n => (i.val + 1) % 2 = r ∧ i.val + 1 < n))
      = (Finset.range n).filter (fun k => (k + 1) % 2 = r ∧ k + 1 < n) := by
    ext k
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, Finset.mem_range,
      true_and]
    constructor
    · intro h
      obtain ⟨i, hpred, rfl⟩ := h
      exact ⟨i.isLt, hpred.1, hpred.2⟩
    · intro h
      obtain ⟨hrange, hpar, hbound⟩ := h
      exact ⟨⟨k, hrange⟩, ⟨hpar, hbound⟩, rfl⟩
  have hcard : (Finset.univ.filter
        (fun i : Fin n => (i.val + 1) % 2 = r ∧ i.val + 1 < n)).card
      = ((Finset.range n).filter (fun k => (k + 1) % 2 = r ∧ k + 1 < n)).card := by
    rw [← himg]
    exact (Finset.card_image_of_injective _ Fin.val_injective).symm
  rw [hcard, range_count n r hr]

private theorem perm_ne_succ (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) (hb : i.val + 1 < n) :
    σ i ≠ σ ⟨i.val + 1, hb⟩ := by
  intro heq
  have hinj2 : i.val = i.val + 1 := Fin.ext_iff.mp (σ.injective heq)
  omega

private theorem rev_gt_flip (n : ℕ) (a b : Fin n) (hne : a ≠ b) :
    (a.rev > b.rev) ↔ ¬(a > b) := by
  constructor
  · intro h1 h2
    have h3 : b < a := h2
    have h4 : a.rev < b.rev := (Fin.rev_lt_rev).mpr h3
    exact absurd h4 (not_lt.mpr (le_of_lt h1))
  · intro hn
    have htri : a < b ∨ b < a := lt_or_gt_of_ne hne
    rcases htri with hlt | hgt
    · exact (Fin.rev_lt_rev).mpr hlt
    · exact absurd hgt hn

private theorem desc_compl (n r : ℕ) (hr : r < 2) (σ : Equiv.Perm (Fin n)) :
    (Finset.univ.filter fun i : Fin n =>
      if h : i.val + 1 < n then ((i.val + 1) % 2 = r ∧ σ i > σ ⟨i.val + 1, h⟩)
      else False).card
    + (Finset.univ.filter fun i : Fin n =>
      if h : i.val + 1 < n then
        ((i.val + 1) % 2 = r ∧
          ((Fin.revPerm : Equiv.Perm (Fin n)) * σ) i >
            ((Fin.revPerm : Equiv.Perm (Fin n)) * σ) ⟨i.val + 1, h⟩)
      else False).card
    = (n + r - 1) / 2 := by
  set A := Finset.univ.filter (fun i : Fin n =>
      if h : i.val + 1 < n then ((i.val + 1) % 2 = r ∧ σ i > σ ⟨i.val + 1, h⟩)
      else False) with hA
  set B := Finset.univ.filter (fun i : Fin n =>
      if h : i.val + 1 < n then
        ((i.val + 1) % 2 = r ∧
          ((Fin.revPerm : Equiv.Perm (Fin n)) * σ) i >
            ((Fin.revPerm : Equiv.Perm (Fin n)) * σ) ⟨i.val + 1, h⟩)
      else False) with hB
  set S := Finset.univ.filter (fun i : Fin n => (i.val + 1) % 2 = r ∧ i.val + 1 < n) with hS
  have hScard : S.card = (n + r - 1) / 2 := fin_count n r hr
  have hne : ∀ i : Fin n, ∀ hb : i.val + 1 < n,
      σ i ≠ σ ⟨i.val + 1, hb⟩ := fun i hb => perm_ne_succ n σ i hb
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro i hai hbi
    simp only [hA, hB, Finset.mem_filter, Finset.mem_univ, true_and] at hai hbi
    by_cases hb : i.val + 1 < n
    · rw [dite_eq_left hb] at hai hbi
      obtain ⟨hpar1, hd1⟩ := hai
      obtain ⟨hpar2, hd2⟩ := hbi
      simp only [Equiv.Perm.mul_apply, Fin.revPerm_apply] at hd2
      exact ((rev_gt_flip n _ _ (hne i hb)).mp hd2) hd1
    · rw [dite_eq_right hb] at hai
      exact hai
  have hunion : A ∪ B = S := by
    ext i
    simp only [hA, hB, hS, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      rcases h with hA' | hB'
      · by_cases hb : i.val + 1 < n
        · rw [dite_eq_left hb] at hA'
          exact ⟨hA'.1, hb⟩
        · rw [dite_eq_right hb] at hA'
          exact hA'.elim
      · by_cases hb : i.val + 1 < n
        · rw [dite_eq_left hb] at hB'
          exact ⟨hB'.1, hb⟩
        · rw [dite_eq_right hb] at hB'
          exact hB'.elim
    · intro hS'
      obtain ⟨hpar, hb⟩ := hS'
      by_cases hd : σ i > σ ⟨i.val + 1, hb⟩
      · left
        rw [dite_eq_left hb]
        exact ⟨hpar, hd⟩
      · right
        rw [dite_eq_left hb]
        refine ⟨hpar, ?_⟩
        simp only [Equiv.Perm.mul_apply, Fin.revPerm_apply]
        exact (rev_gt_flip n _ _ (hne i hb)).mpr hd
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion, hScard] at hcard
  omega

private theorem rot_desc_iff (m : ℕ) (σ : Equiv.Perm (Fin (2 * m + 1)))
    (i : Fin (2 * m + 1)) (hb : i.val + 1 < 2 * m + 1) :
    (((Fin.revPerm : Equiv.Perm (Fin (2 * m + 1))) * σ *
        (Fin.revPerm : Equiv.Perm (Fin (2 * m + 1)))) i >
      ((Fin.revPerm : Equiv.Perm (Fin (2 * m + 1))) * σ *
        (Fin.revPerm : Equiv.Perm (Fin (2 * m + 1)))) ⟨i.val + 1, hb⟩)
    ↔ (σ (⟨i.val + 1, hb⟩ : Fin (2 * m + 1)).rev > σ i.rev) := by
  simp only [Equiv.Perm.mul_apply, Fin.revPerm_apply]
  exact Fin.rev_lt_rev

private theorem rot_card (m : ℕ) (p q : ℕ) (hp : p < 2) (hpq : q = 1 - p)
    (σ : Equiv.Perm (Fin (2 * m + 1))) :
    (Finset.univ.filter fun i : Fin (2 * m + 1) =>
      if h : i.val + 1 < 2 * m + 1 then
        ((i.val + 1) % 2 = p ∧
          ((Fin.revPerm : Equiv.Perm (Fin (2 * m + 1))) * σ *
            (Fin.revPerm : Equiv.Perm (Fin (2 * m + 1)))) i >
            ((Fin.revPerm : Equiv.Perm (Fin (2 * m + 1))) * σ *
              (Fin.revPerm : Equiv.Perm (Fin (2 * m + 1)))) ⟨i.val + 1, h⟩)
      else False).card
    = (Finset.univ.filter fun i : Fin (2 * m + 1) =>
      if h : i.val + 1 < 2 * m + 1 then ((i.val + 1) % 2 = q ∧ σ i > σ ⟨i.val + 1, h⟩)
      else False).card := by
  apply Finset.card_bij (fun a ha => (⟨a.val + 1, by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    by_cases hb : a.val + 1 < 2 * m + 1
    · exact hb
    · rw [dite_eq_right hb] at ha
      exact False.elim ha⟩ : Fin (2 * m + 1)).rev)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    by_cases hb : a.val + 1 < 2 * m + 1
    · rw [dite_eq_left hb] at ha
      obtain ⟨hpar, hd⟩ := ha
      have hphi_par : ((((⟨a.val + 1, hb⟩ : Fin (2 * m + 1)).rev).val + 1) % 2) = q := by
        rw [Fin.val_rev, Fin.val_mk]
        omega
      have hphi_b : (⟨a.val + 1, hb⟩ : Fin (2 * m + 1)).rev.val + 1 < 2 * m + 1 := by
        rw [Fin.val_rev, Fin.val_mk]
        omega
      rw [dite_eq_left hphi_b]
      refine ⟨hphi_par, ?_⟩
      have hdesc := (rot_desc_iff m σ a hb).mp hd
      have e2 : (⟨((⟨a.val + 1, hb⟩ : Fin (2 * m + 1)).rev).val + 1, hphi_b⟩ : Fin (2 * m + 1))
          = a.rev := by
        apply Fin.ext
        simp only [Fin.val_rev]
        omega
      rw [e2]
      exact hdesc
    · rw [dite_eq_right hb] at ha
      exact False.elim ha
  · intro a1 ha1 a2 ha2 heq
    have hrr := congrArg Fin.rev heq
    rw [Fin.rev_rev, Fin.rev_rev] at hrr
    have h1v : a1.val + 1 = a2.val + 1 := congrArg Fin.val hrr
    exact Fin.ext (by omega)
  · intro b hbmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hbmem
    by_cases hbb : b.val + 1 < 2 * m + 1
    · rw [dite_eq_left hbb] at hbmem
      obtain ⟨hparb, hdb⟩ := hbmem
      have hab_b : (⟨b.val + 1, hbb⟩ : Fin (2 * m + 1)).rev.val + 1 < 2 * m + 1 := by
        rw [Fin.val_rev, Fin.val_mk]
        omega
      have hab_par : (((⟨b.val + 1, hbb⟩ : Fin (2 * m + 1)).rev).val + 1) % 2 = p := by
        rw [Fin.val_rev, Fin.val_mk]
        omega
      have eA : (⟨((⟨b.val + 1, hbb⟩ : Fin (2 * m + 1)).rev).val + 1, hab_b⟩ : Fin (2 * m + 1)).rev
          = b := by
        apply Fin.ext
        simp only [Fin.val_rev]
        omega
      refine ⟨(⟨b.val + 1, hbb⟩ : Fin (2 * m + 1)).rev, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [dite_eq_left hab_b]
        refine ⟨hab_par, ?_⟩
        have eB : ((⟨b.val + 1, hbb⟩ : Fin (2 * m + 1)).rev).rev
            = (⟨b.val + 1, hbb⟩ : Fin (2 * m + 1)) := Fin.rev_rev _
        have hgoal : (((Fin.revPerm : Equiv.Perm (Fin (2 * m + 1))) * σ *
            (Fin.revPerm : Equiv.Perm (Fin (2 * m + 1))))
              ((⟨b.val + 1, hbb⟩ : Fin (2 * m + 1)).rev) >
            ((Fin.revPerm : Equiv.Perm (Fin (2 * m + 1))) * σ *
              (Fin.revPerm : Equiv.Perm (Fin (2 * m + 1))))
              ⟨((⟨b.val + 1, hbb⟩ : Fin (2 * m + 1)).rev).val + 1, hab_b⟩) := by
          rw [rot_desc_iff, eA, eB]
          exact hdb
        exact hgoal
      · exact eA
    · rw [dite_eq_right hbb] at hbmem
      exact False.elim hbmem

private theorem odd_total (n : ℕ) :
    (Finset.univ.filter (fun i : Fin n => (i.val + 1) % 2 = 1 ∧ i.val + 1 < n)).card = n / 2 := by
  have h := fin_count n 1 (by norm_num)
  have h2 : (n + 1 - 1) / 2 = n / 2 := by omega
  omega

private theorem even_total (n : ℕ) :
    (Finset.univ.filter
        (fun i : Fin n => (i.val + 1) % 2 = 0 ∧ i.val + 1 < n)).card =
      (n - 1) / 2 := by
  have h := fin_count n 0 (by norm_num)
  have h2 : (n + 0 - 1) / 2 = (n - 1) / 2 := by omega
  omega

private theorem odd_compl (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    oddC n (Fin.revPerm * σ) = n / 2 - oddC n σ := by
  have h := desc_compl n 1 (by norm_num) σ
  have e1 : oddC n σ = (Finset.univ.filter fun i : Fin n =>
    if h : i.val + 1 < n then ((i.val + 1) % 2 = 1 ∧ σ i > σ ⟨i.val + 1, h⟩)
    else False).card := rfl
  have e2 : oddC n (Fin.revPerm * σ) = (Finset.univ.filter fun i : Fin n =>
    if h : i.val + 1 < n then ((i.val + 1) % 2 = 1 ∧
      ((Fin.revPerm : Equiv.Perm (Fin n)) * σ) i >
        ((Fin.revPerm : Equiv.Perm (Fin n)) * σ) ⟨i.val + 1, h⟩)
    else False).card := rfl
  have h2 : (n + 1 - 1) / 2 = n / 2 := by omega
  omega

private theorem even_compl (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    evenC n (Fin.revPerm * σ) = (n - 1) / 2 - evenC n σ := by
  have h := desc_compl n 0 (by norm_num) σ
  have e1 : evenC n σ = (Finset.univ.filter fun i : Fin n =>
    if h : i.val + 1 < n then ((i.val + 1) % 2 = 0 ∧ σ i > σ ⟨i.val + 1, h⟩)
    else False).card := rfl
  have e2 : evenC n (Fin.revPerm * σ) = (Finset.univ.filter fun i : Fin n =>
    if h : i.val + 1 < n then ((i.val + 1) % 2 = 0 ∧
      ((Fin.revPerm : Equiv.Perm (Fin n)) * σ) i >
        ((Fin.revPerm : Equiv.Perm (Fin n)) * σ) ⟨i.val + 1, h⟩)
    else False).card := rfl
  have h2 : (n + 0 - 1) / 2 = (n - 1) / 2 := by omega
  omega

private theorem swap_of_rot_odd (m : ℕ) (σ : Equiv.Perm (Fin (2 * m + 1))) :
    oddC (2 * m + 1) (Fin.revPerm * σ * Fin.revPerm) = evenC (2 * m + 1) σ ∧
    evenC (2 * m + 1) (Fin.revPerm * σ * Fin.revPerm) = oddC (2 * m + 1) σ := by
  have h1 := rot_card m 1 0 (by norm_num) (by norm_num) σ
  have h2 := rot_card m 0 1 (by norm_num) (by norm_num) σ
  have e1 : oddC (2 * m + 1) (Fin.revPerm * σ * Fin.revPerm) =
      (Finset.univ.filter fun i : Fin (2 * m + 1) =>
        if h : i.val + 1 < 2 * m + 1 then ((i.val + 1) % 2 = 1 ∧
          ((Fin.revPerm : Equiv.Perm (Fin (2 * m + 1))) * σ *
            (Fin.revPerm : Equiv.Perm (Fin (2 * m + 1)))) i >
            ((Fin.revPerm : Equiv.Perm (Fin (2 * m + 1))) * σ *
              (Fin.revPerm : Equiv.Perm (Fin (2 * m + 1)))) ⟨i.val + 1, h⟩)
        else False).card := rfl
  have e2 : evenC (2 * m + 1) σ =
      (Finset.univ.filter fun i : Fin (2 * m + 1) =>
        if h : i.val + 1 < 2 * m + 1 then
          ((i.val + 1) % 2 = 0 ∧ σ i > σ ⟨i.val + 1, h⟩)
        else False).card := rfl
  have e3 : evenC (2 * m + 1) (Fin.revPerm * σ * Fin.revPerm) =
      (Finset.univ.filter fun i : Fin (2 * m + 1) =>
        if h : i.val + 1 < 2 * m + 1 then ((i.val + 1) % 2 = 0 ∧
          ((Fin.revPerm : Equiv.Perm (Fin (2 * m + 1))) * σ *
            (Fin.revPerm : Equiv.Perm (Fin (2 * m + 1)))) i >
            ((Fin.revPerm : Equiv.Perm (Fin (2 * m + 1))) * σ *
              (Fin.revPerm : Equiv.Perm (Fin (2 * m + 1)))) ⟨i.val + 1, h⟩)
        else False).card := rfl
  have e4 : oddC (2 * m + 1) σ =
      (Finset.univ.filter fun i : Fin (2 * m + 1) =>
        if h : i.val + 1 < 2 * m + 1 then
          ((i.val + 1) % 2 = 1 ∧ σ i > σ ⟨i.val + 1, h⟩)
        else False).card := rfl
  constructor
  · omega
  · omega

private theorem oddC_le (n : ℕ) (σ : Equiv.Perm (Fin n)) : oddC n σ ≤ n / 2 := by
  have h := desc_compl n 1 (by norm_num) σ
  have e1 : oddC n σ = (Finset.univ.filter fun i : Fin n =>
    if h : i.val + 1 < n then ((i.val + 1) % 2 = 1 ∧ σ i > σ ⟨i.val + 1, h⟩)
    else False).card := rfl
  have h2 : (n + 1 - 1) / 2 = n / 2 := by omega
  omega

private theorem evenC_le (n : ℕ) (σ : Equiv.Perm (Fin n)) : evenC n σ ≤ (n - 1) / 2 := by
  have h := desc_compl n 0 (by norm_num) σ
  have e1 : evenC n σ = (Finset.univ.filter fun i : Fin n =>
    if h : i.val + 1 < n then ((i.val + 1) % 2 = 0 ∧ σ i > σ ⟨i.val + 1, h⟩)
    else False).card := rfl
  have h2 : (n + 0 - 1) / 2 = (n - 1) / 2 := by omega
  omega

private def swp (k : ℕ) (p q : ℝ) : ℝ := if k % 2 = 0 then p else q

private def swq (k : ℕ) (p q : ℝ) : ℝ := if k % 2 = 0 then q else p

private theorem swp_zero (p q : ℝ) : swp 0 p q = p := by
  unfold swp
  exact ite_eq_left (by decide)

private theorem swq_zero (p q : ℝ) : swq 0 p q = q := by
  unfold swq
  exact ite_eq_left (by decide)

private theorem swp_succ (k : ℕ) (p q : ℝ) :
    swp (k + 1) p q = swp k q p := by
  unfold swp
  by_cases h : k % 2 = 0
  · rw [ite_eq_right (by omega : ¬ (k + 1) % 2 = 0), ite_eq_left h]
  · rw [ite_eq_left (by omega : (k + 1) % 2 = 0), ite_eq_right h]

private theorem swq_succ (k : ℕ) (p q : ℝ) :
    swq (k + 1) p q = swq k q p := by
  unfold swq
  by_cases h : k % 2 = 0
  · rw [ite_eq_right (by omega : ¬ (k + 1) % 2 = 0), ite_eq_left h]
  · rw [ite_eq_left (by omega : (k + 1) % 2 = 0), ite_eq_right h]

private theorem swp_even (i : ℕ) (p q : ℝ) : swp (2 * i) p q = p := by
  unfold swp
  rw [ite_eq_left (by omega : 2 * i % 2 = 0)]

private theorem swp_odd (i : ℕ) (p q : ℝ) : swp (2 * i + 1) p q = q := by
  unfold swp
  rw [ite_eq_right (by omega : ¬ (2 * i + 1) % 2 = 0)]

private theorem swq_even (i : ℕ) (p q : ℝ) : swq (2 * i) p q = q := by
  unfold swq
  rw [ite_eq_left (by omega : 2 * i % 2 = 0)]

private theorem swq_odd (i : ℕ) (p q : ℝ) : swq (2 * i + 1) p q = p := by
  unfold swq
  rw [ite_eq_right (by omega : ¬ (2 * i + 1) % 2 = 0)]

private def wt {α : Type*} [LinearOrder α] : List α → ℝ → ℝ → ℝ
  | [], _, _ => 1
  | [_], _, _ => 1
  | a :: b :: t, p, q => (if b < a then p else 1) * wt (b :: t) q p

private theorem wt_nil {α : Type*} [LinearOrder α] (p q : ℝ) :
    wt ([] : List α) p q = 1 := rfl

private theorem wt_singleton {α : Type*} [LinearOrder α] (a : α) (p q : ℝ) :
    wt [a] p q = 1 := rfl

private theorem wt_cons_cons {α : Type*} [LinearOrder α] (a b : α)
    (t : List α) (p q : ℝ) :
    wt (a :: b :: t) p q
      = (if b < a then p else 1) * wt (b :: t) q p := rfl

private def Fp (n : ℕ) (p q : ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), p ^ oddC n σ * q ^ evenC n σ

private def G (j : ℕ) (a b : ℝ) : ℝ :=
  if j = 0 then 1 else a * Fp j b a

private theorem G_zero (a b : ℝ) : G 0 a b = 1 := by
  unfold G
  exact ite_eq_left rfl

private theorem G_ne {j : ℕ} (hj : j ≠ 0) (a b : ℝ) :
    G j a b = a * Fp j b a := by
  unfold G
  exact ite_eq_right hj

private theorem wt_map {α β : Type*} [LinearOrder α] [LinearOrder β]
    (g : α → β) (h : ∀ a b : α, g a < g b ↔ a < b) (l : List α)
    (p q : ℝ) : wt (List.map g l) p q = wt l p q := by
  induction l generalizing p q with
  | nil => simp only [List.map_nil, wt_nil]
  | cons a l ih =>
    cases l with
    | nil =>
      clear ih
      rw [List.map_cons, List.map_nil, wt_singleton, wt_singleton]
    | cons b t =>
      rw [List.map_cons, List.map_cons, wt_cons_cons, wt_cons_cons]
      have ih' := ih q p
      rw [List.map_cons] at ih'
      by_cases hb : b < a
      · rw [ite_eq_left ((h b a).mpr hb), ite_eq_left hb, ih']
      · rw [ite_eq_right (mt (h b a).mp hb), ite_eq_right hb, ih']

private def cntO (n : ℕ) (f : Fin n → ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin n =>
    if h : i.val + 1 < n then (i.val + 1) % 2 = 1 ∧ f ⟨i.val + 1, h⟩ < f i
    else False).card

private def cntE (n : ℕ) (f : Fin n → ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin n =>
    if h : i.val + 1 < n then (i.val + 1) % 2 = 0 ∧ f ⟨i.val + 1, h⟩ < f i
    else False).card

private theorem cntO_perm (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    cntO n (fun i => (σ i).val) = oddC n σ := rfl

private theorem cntE_perm (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    cntE n (fun i => (σ i).val) = evenC n σ := rfl

private theorem ofFn_zero_empty (f : Fin 0 → ℕ) : List.ofFn f = [] :=
  List.eq_nil_of_length_eq_zero List.length_ofFn

private theorem cntO_of_le_one {n : ℕ} (f : Fin n → ℕ) (hn : n ≤ 1) :
    cntO n f = 0 := by
  have h : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      ¬(if h' : i.val + 1 < n then
          (i.val + 1) % 2 = 1 ∧ f ⟨i.val + 1, h'⟩ < f i
        else False) := by
    intro i _ hcon
    have hi := i.isLt
    by_cases h' : i.val + 1 < n
    · omega
    · simp only [dite_eq_right h'] at hcon
  unfold cntO
  rw [Finset.filter_false_of_mem h, Finset.card_empty]

private theorem cntE_of_le_one {n : ℕ} (f : Fin n → ℕ) (hn : n ≤ 1) :
    cntE n f = 0 := by
  have h : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      ¬(if h' : i.val + 1 < n then
          (i.val + 1) % 2 = 0 ∧ f ⟨i.val + 1, h'⟩ < f i
        else False) := by
    intro i _ hcon
    have hi := i.isLt
    by_cases h' : i.val + 1 < n
    · omega
    · simp only [dite_eq_right h'] at hcon
  unfold cntE
  rw [Finset.filter_false_of_mem h, Finset.card_empty]

private theorem cnt_step_parity (x r s : ℕ) (hrs : r = 1 - s)
    (hs : s < 2) : (x + 1 + 1) % 2 = r ↔ (x + 1) % 2 = s := by
  by_cases hs0 : s = 0
  · subst hs0
    constructor <;> intro h <;> omega
  · have hs1 : s = 1 := by omega
    subst hs1
    constructor <;> intro h <;> omega

private theorem cnt_step_pred (n' : ℕ) (f : Fin ((n' + 1) + 1) → ℕ)
    (r s : ℕ) (hrs : r = 1 - s) (hs : s < 2) (j : Fin (n' + 1)) :
    (if h' : j.succ.val + 1 < (n' + 1) + 1 then
      (j.succ.val + 1) % 2 = r ∧ f ⟨j.succ.val + 1, h'⟩ < f j.succ
    else False)
    = (if h' : j.val + 1 < n' + 1 then
      (j.val + 1) % 2 = s ∧
      (fun i : Fin (n' + 1) => f i.succ) ⟨j.val + 1, h'⟩
        < (fun i : Fin (n' + 1) => f i.succ) j
    else False) := by
  have hvs := Fin.val_succ j
  by_cases hj : j.val + 1 < n' + 1
  · have hj' : j.succ.val + 1 < (n' + 1) + 1 := by omega
    have eP : (j.succ.val + 1) % 2 = r ↔ (j.val + 1) % 2 = s := by
      rw [hvs]
      exact cnt_step_parity (j.val) r s hrs hs
    have eX : (⟨j.succ.val + 1, hj'⟩ : Fin ((n' + 1) + 1))
        = (⟨j.val + 1, hj⟩ : Fin (n' + 1)).succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
    apply propext
    simp only [dite_eq_left hj', dite_eq_left hj]
    constructor
    · intro hcon
      obtain ⟨hP, hQ⟩ := hcon
      refine ⟨eP.mp hP, ?_⟩
      rw [← eX]
      exact hQ
    · intro hcon
      obtain ⟨hP, hQ⟩ := hcon
      refine ⟨eP.mpr hP, ?_⟩
      rw [eX]
      exact hQ
  · have hj' : ¬ j.succ.val + 1 < (n' + 1) + 1 := by omega
    simp only [dite_eq_right hj', dite_eq_right hj]

private theorem cnt_bridge (n : ℕ) :
    ∀ (f : Fin n → ℕ) (p q : ℝ),
      p ^ cntO n f * q ^ cntE n f = wt (List.ofFn f) p q := by
  induction n with
  | zero =>
    intro f p q
    rw [ofFn_zero_empty f, wt_nil]
    have hO := cntO_of_le_one f (by omega : 0 ≤ 1)
    have hE := cntE_of_le_one f (by omega : 0 ≤ 1)
    rw [hO, hE, pow_zero, pow_zero, mul_one]
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst hn0
      clear ih
      intro f p q
      rw [List.ofFn_succ]
      have htail : List.ofFn (fun i => f i.succ) = [] := by
        apply List.eq_nil_of_length_eq_zero
        exact List.length_ofFn
      rw [htail, wt_singleton]
      have hO := cntO_of_le_one f (by omega : 0 + 1 ≤ 1)
      have hE := cntE_of_le_one f (by omega : 0 + 1 ≤ 1)
      rw [hO, hE, pow_zero, pow_zero, mul_one]
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      intro f p q
      have hv0 : (0 : Fin ((n' + 1) + 1)).val = 0 := Fin.val_zero _
      have h0' : (0 : Fin ((n' + 1) + 1)).val + 1 < (n' + 1) + 1 := by
        omega
      have hpar0 : ((0 : Fin ((n' + 1) + 1)).val + 1) % 2 = 1 := by
        omega
      have hpar0f : (((0 : Fin ((n' + 1) + 1)).val + 1) % 2 = 0)
          = False := by
        apply propext
        constructor
        · intro hcon
          omega
        · intro hcon
          exact False.elim hcon
      have hmk0 : (⟨(0 : Fin ((n' + 1) + 1)).val + 1, h0'⟩ :
          Fin ((n' + 1) + 1)) = 1 := by
        apply Fin.ext
        have e1 : (⟨(0 : Fin ((n' + 1) + 1)).val + 1, h0'⟩ :
            Fin ((n' + 1) + 1)).val
            = (0 : Fin ((n' + 1) + 1)).val + 1 := rfl
        have e2 : (1 : Fin ((n' + 1) + 1)).val = 1 := Fin.val_one _
        omega
      have ht0 : f (Fin.succ (0 : Fin (n' + 1))) = f 1 :=
        congrArg f Fin.succ_zero_eq_one
      have e0 : (if h' : (0 : Fin ((n' + 1) + 1)).val + 1 < (n' + 1) + 1
          then ((0 : Fin ((n' + 1) + 1)).val + 1) % 2 = 1 ∧
            f ⟨(0 : Fin ((n' + 1) + 1)).val + 1, h'⟩ < f 0
          else False) = (f 1 < f 0) := by
        apply propext
        simp only [dite_eq_left h0']
        constructor
        · intro hcon
          rw [hmk0] at hcon
          exact hcon.2
        · intro hQ
          refine ⟨hpar0, ?_⟩
          rw [hmk0]
          exact hQ
      have ht0E : (if (if h' : (0 : Fin ((n' + 1) + 1)).val + 1
          < (n' + 1) + 1
          then ((0 : Fin ((n' + 1) + 1)).val + 1) % 2 = 0 ∧
            f ⟨(0 : Fin ((n' + 1) + 1)).val + 1, h'⟩ < f 0
          else False) then (1:ℕ) else 0) = 0 := by
        apply ite_eq_right
        intro hcon
        simp only [dite_eq_left h0'] at hcon
        exact absurd hcon.1 (by rw [hpar0f]; exact not_false)
      have eO : cntO ((n' + 1) + 1) f = (if f 1 < f 0 then 1 else 0)
          + cntE (n' + 1) (fun i : Fin (n' + 1) => f i.succ) := by
        have htsum : (∑ j : Fin (n' + 1),
            if (if h' : j.succ.val + 1 < (n' + 1) + 1 then
              (j.succ.val + 1) % 2 = 1 ∧ f ⟨j.succ.val + 1, h'⟩ < f j.succ
            else False) then (1:ℕ) else 0)
            = ∑ j : Fin (n' + 1),
            if (if h' : j.val + 1 < n' + 1 then
              (j.val + 1) % 2 = 0 ∧
              (fun i : Fin (n' + 1) => f i.succ) ⟨j.val + 1, h'⟩
                < (fun i : Fin (n' + 1) => f i.succ) j
            else False) then (1:ℕ) else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          simp only [cnt_step_pred n' f 1 0 (by omega) (by omega) j]
        have hcard : (∑ j : Fin (n' + 1),
            if (if h' : j.val + 1 < n' + 1 then
              (j.val + 1) % 2 = 0 ∧
              (fun i : Fin (n' + 1) => f i.succ) ⟨j.val + 1, h'⟩
                < (fun i : Fin (n' + 1) => f i.succ) j
            else False) then (1:ℕ) else 0)
            = cntE (n' + 1) (fun i : Fin (n' + 1) => f i.succ) :=
          (Finset.card_filter _ _).symm
        unfold cntO
        rw [Finset.card_filter, Fin.sum_univ_succ]
        simp only [e0]
        rw [htsum, hcard]
      have eE : cntE ((n' + 1) + 1) f
          = cntO (n' + 1) (fun i : Fin (n' + 1) => f i.succ) := by
        have htsum : (∑ j : Fin (n' + 1),
            if (if h' : j.succ.val + 1 < (n' + 1) + 1 then
              (j.succ.val + 1) % 2 = 0 ∧ f ⟨j.succ.val + 1, h'⟩ < f j.succ
            else False) then (1:ℕ) else 0)
            = ∑ j : Fin (n' + 1),
            if (if h' : j.val + 1 < n' + 1 then
              (j.val + 1) % 2 = 1 ∧
              (fun i : Fin (n' + 1) => f i.succ) ⟨j.val + 1, h'⟩
                < (fun i : Fin (n' + 1) => f i.succ) j
            else False) then (1:ℕ) else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          simp only [cnt_step_pred n' f 0 1 (by omega) (by omega) j]
        have hcard : (∑ j : Fin (n' + 1),
            if (if h' : j.val + 1 < n' + 1 then
              (j.val + 1) % 2 = 1 ∧
              (fun i : Fin (n' + 1) => f i.succ) ⟨j.val + 1, h'⟩
                < (fun i : Fin (n' + 1) => f i.succ) j
            else False) then (1:ℕ) else 0)
            = cntO (n' + 1) (fun i : Fin (n' + 1) => f i.succ) :=
          (Finset.card_filter _ _).symm
        unfold cntE
        rw [Finset.card_filter, Fin.sum_univ_succ]
        rw [ht0E, htsum, hcard, zero_add]
      have hdesc : p ^ (if f 1 < f 0 then 1 else 0)
          = (if f 1 < f 0 then p else 1) := by
        by_cases h : f 1 < f 0
        · rw [ite_eq_left h, ite_eq_left h, pow_one]
        · rw [ite_eq_right h, ite_eq_right h, pow_zero]
      have hwt : wt (f 0 :: List.ofFn (fun i : Fin (n' + 1) => f i.succ)) p q
          = (if f 1 < f 0 then p else 1)
            * wt (List.ofFn (fun i : Fin (n' + 1) => f i.succ)) q p := by
        rw [List.ofFn_succ, wt_cons_cons, ht0]
      have hiht := ih (fun i : Fin (n' + 1) => f i.succ) q p
      rw [eO, eE, pow_add, hdesc, List.ofFn_succ, hwt, ← hiht]
      ring

private noncomputable def Arr {α : Type*} [DecidableEq α] (S : Finset α) :
    Finset (List α) :=
  (S.toList.permutations).toFinset

private theorem arr_mem_iff {α : Type*} [DecidableEq α] (S : Finset α)
    (l : List α) : l ∈ Arr S ↔ List.Perm l S.toList := by
  unfold Arr
  rw [List.mem_toFinset, List.mem_permutations]

private theorem mem_of_arr_mem {α : Type*} [DecidableEq α] {S : Finset α}
    {l : List α} {x : α} (hl : l ∈ Arr S) (hx : x ∈ l) : x ∈ S := by
  have hperm := (arr_mem_iff S l).mp hl
  exact Finset.mem_toList.mp ((List.Perm.mem_iff hperm).mp hx)

private theorem arr_card {α : Type*} [DecidableEq α] (S : Finset α) :
    (Arr S).card = Nat.factorial S.card := by
  have hnodup : S.toList.permutations.Nodup :=
    List.nodup_permutations S.toList (Finset.nodup_toList S)
  unfold Arr
  rw [List.toFinset_card_of_nodup hnodup, List.length_permutations,
    Finset.length_toList]

private theorem arr_empty {α : Type*} [DecidableEq α] :
    Arr (∅ : Finset α) = {[]} := by
  ext l
  simp only [arr_mem_iff, Finset.mem_singleton, Finset.toList_empty,
    List.perm_nil]

private theorem wt_ofFn_perm (n : ℕ) (σ : Equiv.Perm (Fin n)) (p q : ℝ) :
    wt (List.ofFn ⇑σ) p q = p ^ oddC n σ * q ^ evenC n σ := by
  have h1 := wt_map Fin.val (fun a b => Iff.rfl) (List.ofFn ⇑σ) p q
  have hmap : List.map Fin.val (List.ofFn ⇑σ)
      = List.ofFn (Fin.val ∘ ⇑σ) :=
    List.map_ofFn
  rw [hmap] at h1
  have h3 := cnt_bridge n (Fin.val ∘ ⇑σ) p q
  have eO : cntO n (Fin.val ∘ ⇑σ) = oddC n σ := cntO_perm n σ
  have eE : cntE n (Fin.val ∘ ⇑σ) = evenC n σ := cntE_perm n σ
  rw [eO, eE, h1] at h3
  exact h3.symm

private theorem perm_arr_sum (n : ℕ) (p q : ℝ) :
    (∑ σ : Equiv.Perm (Fin n), wt (List.ofFn ⇑σ) p q)
      = ∑ l ∈ Arr (Finset.univ : Finset (Fin n)), wt l p q := by
  apply Finset.sum_bij (fun (σ : Equiv.Perm (Fin n)) _ => List.ofFn ⇑σ)
  · intro σ _
    rw [arr_mem_iff]
    apply List.perm_of_nodup_nodup_toFinset_eq
    · rw [List.nodup_ofFn]
      exact Equiv.injective σ
    · exact Finset.nodup_toList _
    · rw [Finset.toList_toFinset]
      ext x
      rw [List.mem_toFinset, List.mem_ofFn]
      exact ⟨fun _ => Finset.mem_univ x,
        fun _ => ⟨σ.symm x, Equiv.apply_symm_apply σ x⟩⟩
  · intro σ₁ _ σ₂ _ heq
    have hfg := List.ofFn_injective heq
    exact Equiv.coe_fn_injective hfg
  · intro l hl
    have hperm := (arr_mem_iff (Finset.univ : Finset (Fin n)) l).mp hl
    have hlen : l.length = n := by
      have h1 := List.Perm.length_eq hperm
      rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin] at h1
      exact h1
    have hnodup : l.Nodup :=
      (List.Perm.nodup_iff hperm).mpr (Finset.nodup_toList _)
    have hginj : Function.Injective
        (fun i : Fin n => l.get (Fin.cast hlen.symm i)) := by
      intro i₁ i₂ hgi
      have h12 : l.get (Fin.cast hlen.symm i₁)
          = l.get (Fin.cast hlen.symm i₂) := hgi
      have hc := List.Nodup.injective_get hnodup h12
      have hv : i₁.val = i₂.val := by
        have hcval := congrArg Fin.val hc
        simpa using hcval
      exact Fin.ext hv
    have hbij := Finite.injective_iff_bijective.mp hginj
    have hσ : List.ofFn
        ⇑(Equiv.ofBijective (fun i : Fin n => l.get (Fin.cast hlen.symm i))
          hbij) = l := by
      rw [Equiv.coe_ofBijective]
      exact (List.ofFn_congr hlen (List.get l)).symm.trans
        (List.ofFn_get l)
    exact ⟨Equiv.ofBijective _ hbij, Finset.mem_univ _, hσ⟩
  · intro σ _
    rfl

private theorem arr_transfer (S : Finset ℕ) (p q : ℝ) :
    (∑ l ∈ Arr S, wt l p q) = Fp S.card p q := by
  have einj : Function.Injective ⇑(S.orderEmbOfFin rfl) :=
    StrictMono.injective (S.orderEmbOfFin rfl).strictMono
  have himg : Finset.image (List.map ⇑(S.orderEmbOfFin rfl))
        (Arr (Finset.univ : Finset (Fin S.card))) = Arr S := by
    apply Finset.eq_of_subset_of_card_le
    · intro l hl
      rw [Finset.mem_image] at hl
      obtain ⟨a, ha, rfl⟩ := hl
      rw [arr_mem_iff]
      have hperm := (arr_mem_iff _ _).mp ha
      apply List.perm_of_nodup_nodup_toFinset_eq
      · exact List.Nodup.map einj
          ((List.Perm.nodup_iff hperm).mpr (Finset.nodup_toList _))
      · exact Finset.nodup_toList _
      · have hmem : ∀ j : Fin S.card, j ∈ a := by
          intro j
          exact (List.Perm.mem_iff hperm).mpr
            (Finset.mem_toList.mpr (Finset.mem_univ j))
        have h1 : (List.map ⇑(S.orderEmbOfFin rfl) a).toFinset = S := by
          ext x
          rw [List.mem_toFinset, List.mem_map]
          constructor
          · intro hex
            obtain ⟨j, _, hj⟩ := hex
            rw [← hj]
            exact Finset.orderEmbOfFin_mem S rfl j
          · intro hx
            have hrg := Finset.range_orderEmbOfFin S
              (rfl : S.card = S.card)
            rw [← Finset.mem_coe] at hx
            rw [← hrg] at hx
            have hex : ∃ j : Fin S.card,
                ⇑(S.orderEmbOfFin rfl) j = x := hx
            obtain ⟨j, hj⟩ := hex
            exact ⟨j, hmem j, hj⟩
        rw [h1, Finset.toList_toFinset]
    · rw [Finset.card_image_of_injective _
          (List.map_injective_iff.mpr einj),
        arr_card, arr_card, Finset.card_univ, Fintype.card_fin]
  have hsum : (∑ l ∈ Arr S, wt l p q)
      = ∑ a ∈ Arr (Finset.univ : Finset (Fin S.card)),
        wt (List.map ⇑(S.orderEmbOfFin rfl) a) p q := by
    rw [← himg]
    apply Finset.sum_image
    intro x _ y _ hxy
    exact List.map_injective_iff.mpr einj hxy
  have hwt : ∀ a ∈ Arr (Finset.univ : Finset (Fin S.card)),
      wt (List.map ⇑(S.orderEmbOfFin rfl) a) p q = wt a p q := by
    intro a _
    apply wt_map
    intro x y
    exact OrderEmbedding.lt_iff_lt _
  rw [hsum, Finset.sum_congr rfl hwt]
  have hP := perm_arr_sum S.card p q
  rw [← hP]
  unfold Fp
  apply Finset.sum_congr rfl
  intro σ _
  exact wt_ofFn_perm S.card σ p q

private theorem wt_append_zero (L R : List ℕ) (p q : ℝ)
    (hL : ∀ x ∈ L, 0 < x) :
    wt (L ++ 0 :: R) p q
      = wt L p q * (if L = [] then 1 else swq L.length p q) *
        wt R (swp (L.length + 1) p q) (swq (L.length + 1) p q) := by
  induction L generalizing p q with
  | nil =>
    cases R with
    | nil =>
      change wt ([0] : List ℕ) p q = _
      rw [wt_singleton, wt_nil, wt_nil]
      simp only [ite_true, mul_one]
    | cons r rs =>
      change wt (0 :: r :: rs) p q = _
      rw [wt_cons_cons]
      have hr : ¬ r < (0 : ℕ) := by omega
      rw [ite_eq_right hr, one_mul]
      have e1 : swp ((List.length ([] : List ℕ)) + 1) p q = q := by
        change swp (0 + 1) p q = q
        rw [swp_succ, swp_zero]
      have e2 : swq ((List.length ([] : List ℕ)) + 1) p q = p := by
        change swq (0 + 1) p q = p
        rw [swq_succ, swq_zero]
      rw [wt_nil, e1, e2]
      simp only [ite_true, mul_one, one_mul]
  | cons x xs ih =>
    cases xs with
    | nil =>
      have hx : 0 < x := hL x (List.Mem.head _)
      change wt (x :: 0 :: R) p q = _
      rw [wt_cons_cons, ite_eq_left hx]
      have h1 : wt (0 :: R) q p = wt R p q := by
        have h := ih q p (fun _ hx => by cases hx)
        have e1 : swp ((List.length ([] : List ℕ)) + 1) q p = p := by
          change swp (0 + 1) q p = p
          rw [swp_succ, swp_zero]
        have e2 : swq ((List.length ([] : List ℕ)) + 1) q p = q := by
          change swq (0 + 1) q p = q
          rw [swq_succ, swq_zero]
        rw [wt_nil, e1, e2] at h
        simp only [ite_true, mul_one, one_mul] at h
        exact h
      rw [h1, wt_singleton]
      have hne : (x :: ([] : List ℕ)) ≠ [] := List.cons_ne_nil _ _
      rw [ite_eq_right hne]
      have sq1 : swq (List.length (x :: ([] : List ℕ))) p q = p := by
        change swq (0 + 1) p q = p
        rw [swq_succ, swq_zero]
      have sp2 : swp (List.length (x :: ([] : List ℕ)) + 1) p q = p := by
        change swp ((0 + 1) + 1) p q = p
        rw [swp_succ, swp_succ, swp_zero]
      have sq2 : swq (List.length (x :: ([] : List ℕ)) + 1) p q = q := by
        change swq ((0 + 1) + 1) p q = q
        rw [swq_succ, swq_succ, swq_zero]
      rw [sq1, sp2, sq2]
      simp only [one_mul]
    | cons y ys =>
      have hxs : ∀ x ∈ y :: ys, 0 < x :=
        fun x hx => hL x (List.Mem.tail _ hx)
      change wt (x :: y :: (ys ++ 0 :: R)) p q = _
      rw [wt_cons_cons]
      change (if y < x then p else 1) * wt ((y :: ys) ++ 0 :: R) q p = _
      rw [ih q p hxs]
      have hne_xs : (y :: ys) ≠ [] := List.cons_ne_nil _ _
      rw [ite_eq_right hne_xs]
      have hne_L : (x :: y :: ys) ≠ [] := List.cons_ne_nil _ _
      have hwtL : wt (x :: y :: ys) p q
          = (if y < x then p else 1) * wt (y :: ys) q p := by
        rw [wt_cons_cons]
      rw [hwtL, ite_eq_right hne_L]
      have eswq : swq (List.length (x :: y :: ys)) p q
          = swq (List.length (y :: ys)) q p := by
        change swq (List.length (y :: ys) + 1) p q = _
        rw [swq_succ]
      have eswp : swp (List.length (x :: y :: ys) + 1) p q
          = swp (List.length (y :: ys) + 1) q p := by
        change swp ((List.length (y :: ys) + 1) + 1) p q = _
        rw [swp_succ]
      have eswq2 : swq (List.length (x :: y :: ys) + 1) p q
          = swq (List.length (y :: ys) + 1) q p := by
        change swq ((List.length (y :: ys) + 1) + 1) p q = _
        rw [swq_succ]
      rw [eswq, eswp, eswq2]
      ring

private theorem Fp_zero (p q : ℝ) : Fp 0 p q = 1 := by
  unfold Fp
  have hterm : ∀ σ : Equiv.Perm (Fin 0),
      p ^ oddC 0 σ * q ^ evenC 0 σ = 1 := by
    intro σ
    have hO : oddC 0 σ = 0 := by
      unfold oddC
      simp
    have hE : evenC 0 σ = 0 := by
      unfold evenC
      simp
    rw [hO, hE, pow_zero, pow_zero, mul_one]
  have hcard : Fintype.card (Equiv.Perm (Fin 0)) = 1 := by
    simp
  calc (∑ σ : Equiv.Perm (Fin 0), p ^ oddC 0 σ * q ^ evenC 0 σ)
        = ∑ _x : Equiv.Perm (Fin 0), (1 : ℝ) :=
          Finset.sum_congr rfl (fun σ _ => hterm σ)
      _ = 1 := by
          rw [Finset.sum_const, Finset.card_univ, hcard]
          simp

private theorem Fp_one (p q : ℝ) : Fp 1 p q = 1 := by
  unfold Fp
  have hterm : ∀ σ : Equiv.Perm (Fin 1),
      p ^ oddC 1 σ * q ^ evenC 1 σ = 1 := by
    intro σ
    have hO : oddC 1 σ = 0 := by
      have h := oddC_le 1 σ
      have h2 : (1 : ℕ) / 2 = 0 := by omega
      omega
    have hE : evenC 1 σ = 0 := by
      have h := evenC_le 1 σ
      have h2 : (1 - 1) / 2 = 0 := by omega
      omega
    rw [hO, hE, pow_zero, pow_zero, mul_one]
  have hcard : Fintype.card (Equiv.Perm (Fin 1)) = 1 := by
    simp
  calc (∑ σ : Equiv.Perm (Fin 1), p ^ oddC 1 σ * q ^ evenC 1 σ)
        = ∑ _x : Equiv.Perm (Fin 1), (1 : ℝ) :=
          Finset.sum_congr rfl (fun σ _ => hterm σ)
      _ = 1 := by
          rw [Finset.sum_const, Finset.card_univ, hcard]
          simp

private theorem Fp_odd_symm (m : ℕ) (p q : ℝ) :
    Fp (2 * m + 1) p q = Fp (2 * m + 1) q p := by
  unfold Fp
  have hR2 : (Fin.revPerm : Equiv.Perm (Fin (2 * m + 1))) * Fin.revPerm = 1 := by
    ext x
    simp only [Equiv.Perm.mul_apply, Fin.revPerm_apply, Equiv.Perm.one_apply,
      Fin.rev_rev]
  let R : Equiv.Perm (Fin (2 * m + 1)) := Fin.revPerm
  have hRR : R * R = 1 := hR2
  let e : Equiv.Perm (Fin (2 * m + 1)) ≃ Equiv.Perm (Fin (2 * m + 1)) :=
    { toFun := fun σ => R * σ * R
      invFun := fun σ => R * σ * R
      left_inv := by
        intro σ
        change R * (R * σ * R) * R = σ
        have hcalc : R * (R * σ * R) * R = (R * R) * σ * (R * R) := by group
        rw [hcalc, hRR, one_mul, mul_one]
      right_inv := by
        intro σ
        change R * (R * σ * R) * R = σ
        have hcalc : R * (R * σ * R) * R = (R * R) * σ * (R * R) := by group
        rw [hcalc, hRR, one_mul, mul_one] }
  have hE : (∑ σ : Equiv.Perm (Fin (2 * m + 1)),
        p ^ oddC (2 * m + 1) σ * q ^ evenC (2 * m + 1) σ)
      = (∑ σ : Equiv.Perm (Fin (2 * m + 1)),
        p ^ evenC (2 * m + 1) σ * q ^ oddC (2 * m + 1) σ) := by
    refine Fintype.sum_equiv e _ _ (fun σ => ?_)
    have h1 := (swap_of_rot_odd m σ).1
    have h2 := (swap_of_rot_odd m σ).2
    change p ^ oddC (2 * m + 1) σ * q ^ evenC (2 * m + 1) σ
        = p ^ evenC (2 * m + 1) (R * σ * R) * q ^ oddC (2 * m + 1) (R * σ * R)
    rw [h1, h2]
  rw [hE]
  apply Finset.sum_congr rfl
  intro σ _
  ring

private theorem arr_toFinset {S : Finset ℕ} {l : List ℕ}
    (hl : l ∈ Arr S) : l.toFinset = S := by
  have hperm := (arr_mem_iff S l).mp hl
  have h := List.toFinset_eq_of_perm _ _ hperm
  rwa [Finset.toList_toFinset] at h

private theorem arr_nodup {S : Finset ℕ} {l : List ℕ}
    (hl : l ∈ Arr S) : l.Nodup := by
  have hperm := (arr_mem_iff S l).mp hl
  exact (List.Perm.nodup_iff hperm).mpr (Finset.nodup_toList _)

private theorem mem_arr_of_nodup_toFinset {S : Finset ℕ} {l : List ℕ}
    (hn : l.Nodup) (hs : l.toFinset = S) : l ∈ Arr S := by
  rw [arr_mem_iff]
  apply List.perm_of_nodup_nodup_toFinset_eq hn (Finset.nodup_toList _)
  rw [hs, Finset.toList_toFinset]

private theorem take_drop_zero_eq (l : List ℕ)
    (hk : l.idxOf 0 < l.length) :
    l.take (l.idxOf 0) ++ 0 :: l.drop (l.idxOf 0 + 1) = l := by
  have hget : l[l.idxOf 0] = 0 := List.getElem_idxOf hk
  have hdrop : l.drop (l.idxOf 0)
      = l[l.idxOf 0] :: l.drop (l.idxOf 0 + 1) :=
    List.drop_eq_getElem_cons hk
  have hll : l.take (l.idxOf 0) ++ l.drop (l.idxOf 0) = l :=
    List.take_append_drop _ _
  rw [hdrop, hget] at hll
  exact hll

private theorem idxOf_concat_zero (L R : List ℕ) (h : 0 ∉ L) :
    (L ++ 0 :: R).idxOf 0 = L.length := by
  rw [List.idxOf_append_of_notMem h, List.idxOf_cons_self, Nat.add_zero]

private theorem take_concat_zero (L R : List ℕ) :
    (L ++ 0 :: R).take L.length = L :=
  List.take_left

private theorem drop_concat_zero (L R : List ℕ) :
    (L ++ 0 :: R).drop (L.length + 1) = R := by
  have h1 : (L ++ 0 :: R).drop L.length = 0 :: R := List.drop_left
  have h2 : ((L ++ 0 :: R).drop L.length).drop 1
      = (L ++ 0 :: R).drop (L.length + 1) := List.drop_drop
  rw [← h2, h1]
  simp

private theorem toFinset_concat_zero (L R : List ℕ) :
    (L ++ 0 :: R).toFinset = L.toFinset ∪ insert 0 R.toFinset := by
  simp [List.toFinset_append, List.toFinset_cons]

private theorem nodup_concat_parts {L R : List ℕ}
    (h : (L ++ 0 :: R).Nodup) :
    L.Nodup ∧ 0 ∉ L ∧ 0 ∉ R ∧ R.Nodup ∧ ∀ a ∈ L, ∀ b ∈ R, a ≠ b := by
  rw [List.nodup_append] at h
  obtain ⟨hL, h0R, hdisj⟩ := h
  rw [List.nodup_cons] at h0R
  obtain ⟨h0Rn, hR⟩ := h0R
  refine ⟨hL, ?_, h0Rn, hR, ?_⟩
  · intro hmem
    exact hdisj 0 hmem 0 (List.Mem.head _) rfl
  · intro a ha b hb
    exact hdisj a ha b (List.Mem.tail _ hb)

private theorem nodup_concat_mk {L R : List ℕ}
    (hL : L.Nodup) (hR : R.Nodup) (h0L : 0 ∉ L) (h0R : 0 ∉ R)
    (hd : ∀ a ∈ L, ∀ b ∈ R, a ≠ b) : (L ++ 0 :: R).Nodup := by
  rw [List.nodup_append]
  refine ⟨hL, List.nodup_cons.mpr ⟨h0R, hR⟩, ?_⟩
  intro a ha b hb
  rw [List.mem_cons] at hb
  rcases hb with rfl | hbR
  · intro hcon
    exact h0L (hcon ▸ ha)
  · exact hd a ha b hbR

private theorem fwd_mem (T : Finset ℕ) (h0 : 0 ∉ T) (l : List ℕ)
    (hl : l ∈ Arr (insert 0 T)) :
    (l.take (l.idxOf 0)).toFinset ∈ T.powerset ∧
    (l.take (l.idxOf 0)) ∈ Arr ((l.take (l.idxOf 0)).toFinset) ∧
    (l.drop (l.idxOf 0 + 1)) ∈ Arr (T \ (l.take (l.idxOf 0)).toFinset) := by
  set k := l.idxOf 0 with hk_def
  set L := l.take k with hL_def
  set R := l.drop (k + 1) with hR_def
  have hlNodup : l.Nodup := arr_nodup hl
  have hlFin : l.toFinset = insert 0 T := arr_toFinset hl
  have h0l : 0 ∈ l := by
    have hmem : (0 : ℕ) ∈ l.toFinset := by rw [hlFin]; exact Finset.mem_insert_self 0 T
    exact List.mem_toFinset.mp hmem
  have hk : k < l.length := List.idxOf_lt_length_iff.mpr h0l
  have hsplit : L ++ 0 :: R = l := take_drop_zero_eq l hk
  have hNR : (L ++ 0 :: R).Nodup := by rw [hsplit]; exact hlNodup
  obtain ⟨hLN, h0L, h0R, hRN, hdisj⟩ := nodup_concat_parts hNR
  have hLmem : L ∈ Arr (L.toFinset) :=
    mem_arr_of_nodup_toFinset hLN rfl
  have hsub : L.toFinset ⊆ T := by
    intro x hx
    have hxL : x ∈ L := List.mem_toFinset.mp hx
    have hx0 : x ≠ 0 := fun he => h0L (he ▸ hxL)
    have hxl : x ∈ l := by
      have hmem : x ∈ L ++ 0 :: R := List.mem_append.mpr (Or.inl hxL)
      rwa [hsplit] at hmem
    have hxF : x ∈ insert 0 T := by
      have : x ∈ l.toFinset := List.mem_toFinset.mpr hxl
      rwa [hlFin] at this
    rcases Finset.mem_insert.mp hxF with h | h
    · exact absurd h hx0
    · exact h
  have hReq : R.toFinset = T \ L.toFinset := by
    ext y
    constructor
    · intro hy
      have hyR : y ∈ R := List.mem_toFinset.mp hy
      have hy0 : y ≠ 0 := fun he => h0R (he ▸ hyR)
      have hyl : y ∈ l := by
        have hmem : y ∈ L ++ 0 :: R := by
          rw [List.mem_append]
          exact Or.inr (List.mem_cons.mpr (Or.inr hyR))
        rwa [hsplit] at hmem
      have hyF : y ∈ insert 0 T := by
        have : y ∈ l.toFinset := List.mem_toFinset.mpr hyl
        rwa [hlFin] at this
      have hyT : y ∈ T := by
        rcases Finset.mem_insert.mp hyF with h | h
        · exact absurd h hy0
        · exact h
      have hyNL : y ∉ L.toFinset := by
        intro hyU
        have hyL : y ∈ L := List.mem_toFinset.mp hyU
        exact hdisj y hyL y hyR rfl
      exact Finset.mem_sdiff.mpr ⟨hyT, hyNL⟩
    · intro hy
      have hyT : y ∈ T := (Finset.mem_sdiff.mp hy).1
      have hyNL : y ∉ L.toFinset := (Finset.mem_sdiff.mp hy).2
      have hyL : y ∉ L := fun hm => hyNL (List.mem_toFinset.mpr hm)
      have hy0 : y ≠ 0 := fun he => h0 (he ▸ hyT)
      have hyI : y ∈ insert 0 T := Finset.mem_insert.mpr (Or.inr hyT)
      have hyl : y ∈ l := by
        have : y ∈ l.toFinset := by rw [hlFin]; exact hyI
        exact List.mem_toFinset.mp this
      have hmem : y ∈ L ++ 0 :: R := by rw [hsplit]; exact hyl
      rw [List.mem_append, List.mem_cons] at hmem
      rcases hmem with hLy | rfl | hRy
      · exact absurd hLy hyL
      · exact absurd rfl hy0
      · exact List.mem_toFinset.mpr hRy
  have hRmem : R ∈ Arr (T \ L.toFinset) :=
    mem_arr_of_nodup_toFinset hRN hReq
  exact ⟨Finset.mem_powerset.mpr hsub, hLmem, hRmem⟩

private theorem bwd_mem (T : Finset ℕ) (h0 : 0 ∉ T) (U : Finset ℕ)
    (hU : U ∈ T.powerset) (L R : List ℕ)
    (hL : L ∈ Arr U) (hR : R ∈ Arr (T \ U)) :
    (L ++ 0 :: R) ∈ Arr (insert 0 T) := by
  have hLN : L.Nodup := arr_nodup hL
  have hRN : R.Nodup := arr_nodup hR
  have hLF : L.toFinset = U := arr_toFinset hL
  have hRF : R.toFinset = T \ U := arr_toFinset hR
  have hUsub : U ⊆ T := Finset.mem_powerset.mp hU
  have h0L : 0 ∉ L := by
    intro hm
    exact h0 (hUsub (hLF ▸ List.mem_toFinset.mpr hm))
  have h0R : 0 ∉ R := by
    intro hm
    have hmem : (0 : ℕ) ∈ T \ U := hRF ▸ List.mem_toFinset.mpr hm
    exact h0 (Finset.mem_sdiff.mp hmem).1
  have hdisj : ∀ a ∈ L, ∀ b ∈ R, a ≠ b := by
    intro a ha b hb hab
    have haU : a ∈ U := hLF ▸ List.mem_toFinset.mpr ha
    have hbS : a ∈ T \ U := hab ▸ (hRF ▸ List.mem_toFinset.mpr hb)
    exact (Finset.mem_sdiff.mp hbS).2 haU
  have hNodup : (L ++ 0 :: R).Nodup := nodup_concat_mk hLN hRN h0L h0R hdisj
  have hFin : (L ++ 0 :: R).toFinset = insert 0 T := by
    rw [toFinset_concat_zero, hLF, hRF]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_sdiff]
    constructor
    · rintro (hxU | rfl | ⟨hxT, -⟩)
      · exact Or.inr (hUsub hxU)
      · exact Or.inl rfl
      · exact Or.inr hxT
    · rintro (rfl | hxT)
      · exact Or.inr (Or.inl rfl)
      · by_cases hxU : x ∈ U
        · exact Or.inl hxU
        · exact Or.inr (Or.inr ⟨hxT, hxU⟩)
  exact mem_arr_of_nodup_toFinset hNodup hFin

private theorem sigma_collapse (T : Finset ℕ) (f : List ℕ → ℝ) :
    (∑ U ∈ T.powerset, ∑ L ∈ Arr U, ∑ R ∈ Arr (T \ U), f (L ++ 0 :: R))
      = ∑ x ∈ (T.powerset).sigma (fun U => (Arr U) ×ˢ (Arr (T \ U))),
          f (x.2.1 ++ 0 :: x.2.2) := by
  have hinner : ∀ U ∈ T.powerset, (∑ L ∈ Arr U, ∑ R ∈ Arr (T \ U), f (L ++ 0 :: R))
      = ∑ p ∈ (Arr U) ×ˢ (Arr (T \ U)), f (p.1 ++ 0 :: p.2) := by
    intro U _
    exact (Finset.sum_product' _ _ _).symm
  calc (∑ U ∈ T.powerset, ∑ L ∈ Arr U, ∑ R ∈ Arr (T \ U), f (L ++ 0 :: R))
        = ∑ U ∈ T.powerset, ∑ p ∈ (Arr U) ×ˢ (Arr (T \ U)), f (p.1 ++ 0 :: p.2) :=
          Finset.sum_congr rfl (fun U hU => hinner U hU)
      _ = _ := Finset.sum_sigma' _ _ _

private theorem arr_insert_zero_sum (T : Finset ℕ) (h0 : 0 ∉ T)
    (f : List ℕ → ℝ) :
    ∑ l ∈ Arr (insert 0 T), f l
      = ∑ U ∈ T.powerset, ∑ L ∈ Arr U, ∑ R ∈ Arr (T \ U), f (L ++ 0 :: R) := by
  rw [sigma_collapse]
  apply Finset.sum_nbij'
    (fun l => (⟨(l.take (l.idxOf 0)).toFinset,
      ((l.take (l.idxOf 0)), (l.drop (l.idxOf 0 + 1)))⟩ :
      Sigma (fun _ => List ℕ × List ℕ)))
    (fun x => x.2.1 ++ 0 :: x.2.2)
  · intro l hl
    obtain ⟨hU, hL, hR⟩ := fwd_mem T h0 l hl
    exact Finset.mem_sigma.mpr ⟨hU, Finset.mem_product.mpr ⟨hL, hR⟩⟩
  · intro x hx
    obtain ⟨hU, hpair⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hL, hR⟩ := Finset.mem_product.mp hpair
    exact bwd_mem T h0 x.1 hU x.2.1 x.2.2 hL hR
  · intro l hl
    have hlFin : l.toFinset = insert 0 T := arr_toFinset hl
    have h0l : 0 ∈ l := by
      have hmem : (0 : ℕ) ∈ l.toFinset := by
        rw [hlFin]; exact Finset.mem_insert_self 0 T
      exact List.mem_toFinset.mp hmem
    have hk : l.idxOf 0 < l.length := List.idxOf_lt_length_iff.mpr h0l
    change l.take (l.idxOf 0) ++ 0 :: l.drop (l.idxOf 0 + 1) = l
    exact take_drop_zero_eq l hk
  · intro x hx
    obtain ⟨U, L, R⟩ := x
    obtain ⟨hU, hpair⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hL, hR⟩ := Finset.mem_product.mp hpair
    have hUsub : U ⊆ T := Finset.mem_powerset.mp hU
    have hLF : L.toFinset = U := arr_toFinset hL
    have h0L : 0 ∉ L := by
      intro hm
      exact h0 (hUsub (hLF ▸ List.mem_toFinset.mpr hm))
    have hidx : (L ++ 0 :: R).idxOf 0 = L.length :=
      idxOf_concat_zero L R h0L
    have htake : (L ++ 0 :: R).take ((L ++ 0 :: R).idxOf 0) = L := by
      rw [hidx]; exact take_concat_zero L R
    have hdrop : (L ++ 0 :: R).drop ((L ++ 0 :: R).idxOf 0 + 1) = R := by
      rw [hidx]; exact drop_concat_zero L R
    have hfin : ((L ++ 0 :: R).take ((L ++ 0 :: R).idxOf 0)).toFinset = U := by
      rw [htake]; exact hLF
    change (⟨((L ++ 0 :: R).take ((L ++ 0 :: R).idxOf 0)).toFinset,
        (((L ++ 0 :: R).take ((L ++ 0 :: R).idxOf 0)),
          ((L ++ 0 :: R).drop ((L ++ 0 :: R).idxOf 0 + 1)))⟩ :
        Sigma (fun _ => List ℕ × List ℕ)) = ⟨U, (L, R)⟩
    rw [hfin, htake, hdrop]
  · intro l hl
    have hlFin : l.toFinset = insert 0 T := arr_toFinset hl
    have h0l : 0 ∈ l := by
      have hmem : (0 : ℕ) ∈ l.toFinset := by
        rw [hlFin]; exact Finset.mem_insert_self 0 T
      exact List.mem_toFinset.mp hmem
    have hk : l.idxOf 0 < l.length := List.idxOf_lt_length_iff.mpr h0l
    change f l = f (l.take (l.idxOf 0) ++ 0 :: l.drop (l.idxOf 0 + 1))
    rw [take_drop_zero_eq l hk]

private def recTerm (n k : ℕ) (p q : ℝ) : ℝ :=
  (n.choose k : ℝ) * Fp k p q * (if k = 0 then 1 else swq k p q) *
    Fp (n - k) (swp (k + 1) p q) (swq (k + 1) p q)

private theorem arr_length_eq_card (U : Finset ℕ) (L : List ℕ)
    (hL : L ∈ Arr U) : L.length = U.card := by
  have hperm := (arr_mem_iff U L).mp hL
  rw [List.Perm.length_eq hperm, Finset.length_toList]

private theorem wt_pos_of_arr_powerset (T U : Finset ℕ) (h0 : 0 ∉ T)
    (L : List ℕ) (hU : U ∈ T.powerset) (hL : L ∈ Arr U) (x : ℕ)
    (hx : x ∈ L) : 0 < x := by
  have hLF : L.toFinset = U := arr_toFinset hL
  have hxU : x ∈ U := hLF ▸ List.mem_toFinset.mpr hx
  have hxT : x ∈ T := (Finset.mem_powerset.mp hU) hxU
  have hxne : x ≠ 0 := by
    intro he
    rw [he] at hxT
    exact h0 hxT
  exact Nat.pos_of_ne_zero hxne

private theorem wt_split_eq (U : Finset ℕ) (L R : List ℕ) (p q : ℝ)
    (hpos : ∀ x ∈ L, 0 < x) (hlen : L.length = U.card) :
    wt (L ++ 0 :: R) p q
      = wt L p q * (if U.card = 0 then 1 else swq U.card p q) *
        wt R (swp (U.card + 1) p q) (swq (U.card + 1) p q) := by
  have h := wt_append_zero L R p q hpos
  have hif : (if L = [] then (1 : ℝ) else swq L.length p q)
      = (if U.card = 0 then 1 else swq U.card p q) := by
    by_cases hL : L = []
    · subst hL
      simp at hlen
      rw [ite_eq_left rfl, ite_eq_left hlen.symm]
    · have hcard : U.card ≠ 0 := by
        intro hc
        apply hL
        rw [← List.length_eq_zero_iff]
        omega
      rw [ite_eq_right hL, ite_eq_right hcard, hlen]
  rw [hif] at h
  rw [hlen] at h
  exact h

private theorem sum_pair_factor (T U : Finset ℕ) (hU : U ∈ T.powerset)
    (h0 : 0 ∉ T) (p q : ℝ) :
    (∑ L ∈ Arr U, ∑ R ∈ Arr (T \ U), wt (L ++ 0 :: R) p q)
      = Fp U.card p q * (if U.card = 0 then 1 else swq U.card p q) *
        Fp (T.card - U.card) (swp (U.card + 1) p q) (swq (U.card + 1) p q) := by
  have hrewrite : ∀ L ∈ Arr U, ∀ R ∈ Arr (T \ U),
      wt (L ++ 0 :: R) p q
        = (wt L p q * (if U.card = 0 then 1 else swq U.card p q)) *
          wt R (swp (U.card + 1) p q) (swq (U.card + 1) p q) := by
    intro L hL R _
    have hpos : ∀ x ∈ L, 0 < x :=
      fun x hx => wt_pos_of_arr_powerset T U h0 L hU hL x hx
    have hlen : L.length = U.card := arr_length_eq_card U L hL
    exact wt_split_eq U L R p q hpos hlen
  have hsub : U ⊆ T := Finset.mem_powerset.mp hU
  have hcard : (T \ U).card = T.card - U.card :=
    Finset.card_sdiff_of_subset hsub
  calc (∑ L ∈ Arr U, ∑ R ∈ Arr (T \ U), wt (L ++ 0 :: R) p q)
        = ∑ L ∈ Arr U, ∑ R ∈ Arr (T \ U),
            ((wt L p q * (if U.card = 0 then 1 else swq U.card p q)) *
              wt R (swp (U.card + 1) p q) (swq (U.card + 1) p q)) :=
          Finset.sum_congr rfl (fun L hL =>
            Finset.sum_congr rfl (fun R hR => hrewrite L hL R hR))
      _ = (∑ L ∈ Arr U, (wt L p q * (if U.card = 0 then 1 else swq U.card p q))) *
            ∑ R ∈ Arr (T \ U), wt R (swp (U.card + 1) p q) (swq (U.card + 1) p q) := by
          exact (Finset.sum_mul_sum _ _ _ _).symm
      _ = ((∑ L ∈ Arr U, wt L p q) * (if U.card = 0 then 1 else swq U.card p q)) *
            ∑ R ∈ Arr (T \ U), wt R (swp (U.card + 1) p q) (swq (U.card + 1) p q) := by
          congr 1
          exact (Finset.sum_mul _ _ _).symm
      _ = _ := by
          rw [arr_transfer U p q, arr_transfer (T \ U),
            hcard]

private theorem Fp_succ_recursion (n : ℕ) (p q : ℝ) :
    Fp (n + 1) p q = ∑ k ∈ Finset.range (n + 1), recTerm n k p q := by
  have hcard : (Finset.range (n + 1)).card = n + 1 := Finset.card_range _
  have hFp : Fp (n + 1) p q = ∑ l ∈ Arr (Finset.range (n + 1)), wt l p q := by
    conv_lhs => rw [← hcard]
    exact (arr_transfer _ _ _).symm
  set T := (Finset.range (n + 1)).erase 0 with hTdef
  have h0mem : 0 ∈ Finset.range (n + 1) :=
    Finset.mem_range.mpr (Nat.succ_pos n)
  have hins : insert 0 T = Finset.range (n + 1) := Finset.insert_erase h0mem
  have h0T : 0 ∉ T := Finset.notMem_erase 0 _
  have hTcard : T.card = n := by
    rw [hTdef, Finset.card_erase_of_mem h0mem, Finset.card_range,
      Nat.add_sub_cancel]
  rw [hFp]
  have hsplit : (∑ l ∈ Arr (Finset.range (n + 1)), wt l p q)
      = ∑ U ∈ T.powerset, ∑ L ∈ Arr U, ∑ R ∈ Arr (T \ U),
        wt (L ++ 0 :: R) p q := by
    conv_lhs => rw [← hins]
    exact arr_insert_zero_sum T h0T (fun l => wt l p q)
  rw [hsplit]
  have hper : ∀ U ∈ T.powerset,
      (∑ L ∈ Arr U, ∑ R ∈ Arr (T \ U), wt (L ++ 0 :: R) p q)
        = Fp U.card p q * (if U.card = 0 then 1 else swq U.card p q) *
          Fp (T.card - U.card) (swp (U.card + 1) p q) (swq (U.card + 1) p q) := by
    intro U hU
    exact sum_pair_factor T U hU h0T p q
  have hLHS : (∑ U ∈ T.powerset, ∑ L ∈ Arr U, ∑ R ∈ Arr (T \ U),
        wt (L ++ 0 :: R) p q)
      = ∑ U ∈ T.powerset, (Fp U.card p q * (if U.card = 0 then 1 else swq U.card p q) *
          Fp (T.card - U.card) (swp (U.card + 1) p q) (swq (U.card + 1) p q)) :=
    Finset.sum_congr rfl (fun U hU => hper U hU)
  rw [hLHS]
  have hpow : (∑ U ∈ T.powerset, (Fp U.card p q *
        (if U.card = 0 then 1 else swq U.card p q) *
        Fp (T.card - U.card) (swp (U.card + 1) p q) (swq (U.card + 1) p q)))
      = ∑ m ∈ Finset.range (T.card + 1), (T.card.choose m) •
          (Fp m p q * (if m = 0 then 1 else swq m p q) *
            Fp (T.card - m) (swp (m + 1) p q) (swq (m + 1) p q)) := by
    exact Finset.sum_powerset_apply_card (fun k => Fp k p q *
      (if k = 0 then 1 else swq k p q) *
      Fp (T.card - k) (swp (k + 1) p q) (swq (k + 1) p q))
  rw [hpow, hTcard]
  apply Finset.sum_congr rfl
  intro k _
  unfold recTerm
  rw [nsmul_eq_mul]
  ring

private theorem recTerm_middle_swap (m : ℕ)
    (H : ∀ i : ℕ, 1 ≤ i → i ≤ m → ∀ p q : ℝ,
      (1 + q) * Fp (2 * i) p q = (1 + p) * Fp (2 * i) q p)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 2 * m) (p q : ℝ) :
    (1 + q) * recTerm (2 * m + 1) k p q
      = (1 + p) * recTerm (2 * m + 1) (2 * m + 1 - k) q p := by
  rcases Nat.even_or_odd' k with ⟨i, rfl | rfl⟩
  · have hi1 : 1 ≤ i := by omega
    have hi2 : i ≤ m := by omega
    have hkk : 2 * i ≠ 0 := by omega
    have hle : 2 * i ≤ 2 * m + 1 := by omega
    have hk' : 2 * m + 1 - 2 * i = 2 * (m - i) + 1 := by omega
    have hkk' : 2 * (m - i) + 1 ≠ 0 := by omega
    have htail : 2 * m + 1 - (2 * (m - i) + 1) = 2 * i := by omega
    have harg : 2 * (m - i) + 1 + 1 = 2 * ((m - i) + 1) := by omega
    have hchoose : (2 * m + 1).choose (2 * i)
        = (2 * m + 1).choose (2 * m + 1 - 2 * i) :=
      (Nat.choose_symm hle).symm
    have hH := H i hi1 hi2 p q
    unfold recTerm
    rw [ite_eq_right hkk, hchoose, hk', ite_eq_right hkk',
      swq_even i p q, swp_odd i p q, swq_odd i p q,
      swq_odd (m - i) q p, htail, harg,
      swp_even ((m - i) + 1) q p, swq_even ((m - i) + 1) q p]
    linear_combination
      (2 * m + 1).choose (2 * (m - i) + 1) * q *
        Fp (2 * (m - i) + 1) q p * hH
  · have hjm1 : 1 ≤ m - i := by omega
    have hjm2 : m - i ≤ m := by omega
    have hkk : 2 * i + 1 ≠ 0 := by omega
    have hle : 2 * i + 1 ≤ 2 * m + 1 := by omega
    have hk' : 2 * m + 1 - (2 * i + 1) = 2 * (m - i) := by omega
    have hkk' : 2 * (m - i) ≠ 0 := by omega
    have htail : 2 * m + 1 - 2 * (m - i) = 2 * i + 1 := by omega
    have harg2 : 2 * i + 1 + 1 = 2 * (i + 1) := by omega
    have hchoose : (2 * m + 1).choose (2 * i + 1)
        = (2 * m + 1).choose (2 * m + 1 - (2 * i + 1)) :=
      (Nat.choose_symm hle).symm
    have hH := H (m - i) hjm1 hjm2 p q
    unfold recTerm
    rw [ite_eq_right hkk, hchoose, hk', ite_eq_right hkk',
      swq_odd i p q, harg2, swp_even (i + 1) p q, swq_even (i + 1) p q,
      swq_even (m - i) q p, htail,
      swp_odd (m - i) q p, swq_odd (m - i) q p]
    linear_combination
      (2 * m + 1).choose (2 * (m - i)) * p *
        Fp (2 * i + 1) p q * hH

private theorem recTerm_endpoints (m : ℕ) (p q : ℝ) :
    (1 + q) * (recTerm (2 * m + 1) 0 p q + recTerm (2 * m + 1) (2 * m + 1) p q)
      = (1 + p) * (recTerm (2 * m + 1) 0 q p
        + recTerm (2 * m + 1) (2 * m + 1) q p) := by
  have h0 : recTerm (2 * m + 1) 0 p q = Fp (2 * m + 1) q p := by
    unfold recTerm
    rw [Nat.choose_zero_right, Fp_zero, Nat.sub_zero,
      ite_eq_left rfl, swp_succ, swp_zero, swq_succ, swq_zero]
    simp
  have h1 : recTerm (2 * m + 1) (2 * m + 1) p q
      = Fp (2 * m + 1) p q * p := by
    unfold recTerm
    rw [Nat.choose_self, Nat.sub_self, Fp_zero,
      ite_eq_right (by omega : 2 * m + 1 ≠ 0), swq_odd m p q]
    ring
  have h0' : recTerm (2 * m + 1) 0 q p = Fp (2 * m + 1) p q := by
    unfold recTerm
    rw [Nat.choose_zero_right, Fp_zero, Nat.sub_zero,
      ite_eq_left rfl, swp_succ, swp_zero, swq_succ, swq_zero]
    simp
  have h1' : recTerm (2 * m + 1) (2 * m + 1) q p
      = Fp (2 * m + 1) q p * q := by
    unfold recTerm
    rw [Nat.choose_self, Nat.sub_self, Fp_zero,
      ite_eq_right (by omega : 2 * m + 1 ≠ 0), swq_odd m q p]
    ring
  have hsym := Fp_odd_symm m p q
  rw [h0, h1, h0', h1', hsym]
  ring

private theorem Fp_even_symm : ∀ (m : ℕ) (p q : ℝ),
    (1 + q) * Fp (2 * m + 2) p q = (1 + p) * Fp (2 * m + 2) q p := by
  intro m
  refine Nat.strong_induction_on m ?_
  intro m ih p q
  have H : ∀ i : ℕ, 1 ≤ i → i ≤ m → ∀ a b : ℝ,
      (1 + b) * Fp (2 * i) a b = (1 + a) * Fp (2 * i) b a := by
    intro i hi1 hi2 a b
    have hi_eq : 2 * i = 2 * (i - 1) + 2 := by omega
    have hlt : i - 1 < m := by omega
    have hih := ih (i - 1) hlt a b
    rwa [← hi_eq] at hih
  have e1 : 2 * m + 1 + 1 = 2 * m + 2 := by omega
  have hL := Fp_succ_recursion (2 * m + 1) p q
  have hR := Fp_succ_recursion (2 * m + 1) q p
  rw [e1] at hL hR
  rw [hL, hR, Finset.mul_sum, Finset.mul_sum]
  have e2 : 2 * m + 2 = (2 * m + 1) + 1 := by omega
  rw [e2]
  conv_lhs => rw [Finset.sum_range_succ, Finset.sum_range_succ']
  conv_rhs => rw [Finset.sum_range_succ, Finset.sum_range_succ']
  have hreflect : (∑ j ∈ Finset.range (2 * m),
        (1 + p) * recTerm (2 * m + 1) (j + 1) q p)
      = ∑ j ∈ Finset.range (2 * m),
        (1 + p) * recTerm (2 * m + 1) (2 * m - j) q p := by
    have h := Finset.sum_range_reflect
      (fun j => (1 + p) * recTerm (2 * m + 1) (j + 1) q p) (2 * m)
    rw [← h]
    apply Finset.sum_congr rfl
    intro j hj
    have hj2 : j < 2 * m := Finset.mem_range.mp hj
    have e : 2 * m - 1 - j + 1 = 2 * m - j := by omega
    rw [e]
  conv_rhs => rw [hreflect]
  have hmid : (∑ j ∈ Finset.range (2 * m),
        (1 + q) * recTerm (2 * m + 1) (j + 1) p q)
      = ∑ j ∈ Finset.range (2 * m),
        (1 + p) * recTerm (2 * m + 1) (2 * m - j) q p := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj2 : j < 2 * m := Finset.mem_range.mp hj
    have hk1 : 1 ≤ j + 1 := by omega
    have hk2 : j + 1 ≤ 2 * m := by omega
    have hN := recTerm_middle_swap m H (j + 1) hk1 hk2 p q
    have e : 2 * m + 1 - (j + 1) = 2 * m - j := by omega
    rwa [e] at hN
  have hend : (1 + q) * recTerm (2 * m + 1) 0 p q
        + (1 + q) * recTerm (2 * m + 1) (2 * m + 1) p q
      = (1 + p) * recTerm (2 * m + 1) 0 q p
        + (1 + p) * recTerm (2 * m + 1) (2 * m + 1) q p := by
    linear_combination recTerm_endpoints m p q
  linear_combination hmid + hend

/--
**Palindromicity of the refined Eulerian polynomials.** Let $n \ge 1$. For a permutation
$\sigma$ of $\{1, \dots, n\}$, let $\mathrm{odes}(\sigma)$ (resp. $\mathrm{edes}(\sigma)$) be the
number of odd (resp. even) positions $i \in \{1, \dots, n-1\}$ with $\sigma(i) > \sigma(i+1)$,
and let $A_n(p, q) = \sum_{\sigma} p^{\mathrm{odes}(\sigma)} q^{\mathrm{edes}(\sigma)}$, the sum
over all permutations $\sigma$ of $\{1, \dots, n\}$, be the refined Eulerian polynomial with real
coefficients. Let $P_n = (1+q) A_n$ if $n$ is even and $P_n = A_n$ if $n$ is odd. Then $P_n$ is
palindromic of darga $\lfloor n/2 \rfloor$: it is a nonzero polynomial, $P_n(p, q) = P_n(q, p)$
for all real $p$ and $q$, and $P_n(p, q) = (pq)^{\lfloor n/2 \rfloor} P_n(1/p, 1/q)$ for all
nonzero real $p$ and $q$.

Proves `Wanted` entry `refinedEulerianPolynomial_palindromic`.

Source: Hua Sun, "A New Class of Refined Eulerian Polynomials," Journal of Integer Sequences
21 (2018), Article 18.5.5, Theorem (label pal), lines 160–162
(polynomial definition lines 135–136, palindromic-darga definition lines 105–110).
`https://cs.uwaterloo.ca/journals/JIS/VOL21/Sun/sun2.tex`
-/
theorem refinedEulerianPolynomial_palindromic
    (n : ℕ) (hn : 1 ≤ n) :
    let oddDescentCount : Equiv.Perm (Fin n) → ℕ := fun σ =>
      (Finset.univ.filter fun i : Fin n =>
        if h : i.val + 1 < n then
          (i.val + 1) % 2 = 1 ∧ σ i > σ ⟨i.val + 1, h⟩
        else False).card
    let evenDescentCount : Equiv.Perm (Fin n) → ℕ := fun σ =>
      (Finset.univ.filter fun i : Fin n =>
        if h : i.val + 1 < n then
          (i.val + 1) % 2 = 0 ∧ σ i > σ ⟨i.val + 1, h⟩
        else False).card
    let refinedEulerian : Polynomial (Polynomial ℝ) :=
      ∑ σ : Equiv.Perm (Fin n),
        Polynomial.C (Polynomial.X ^ evenDescentCount σ) *
          Polynomial.X ^ oddDescentCount σ
    let palindromicRefinement : Polynomial (Polynomial ℝ) :=
      if n % 2 = 0 then Polynomial.C (1 + Polynomial.X) * refinedEulerian
      else refinedEulerian
    palindromicRefinement ≠ 0 ∧
      (∀ p q : ℝ,
        Polynomial.eval q (Polynomial.eval (Polynomial.C p) palindromicRefinement) =
          Polynomial.eval p (Polynomial.eval (Polynomial.C q) palindromicRefinement)) ∧
      ∀ p q : ℝ, p ≠ 0 → q ≠ 0 →
        Polynomial.eval q (Polynomial.eval (Polynomial.C p) palindromicRefinement) =
          (p * q) ^ (n / 2) *
            Polynomial.eval q⁻¹
              (Polynomial.eval (Polynomial.C p⁻¹) palindromicRefinement) := by
  intro oddDescentCount evenDescentCount refinedEulerian palindromicRefinement
  have hodd : ∀ σ, oddDescentCount σ = oddC n σ := fun σ => rfl
  have heven : ∀ σ, evenDescentCount σ = evenC n σ := fun σ => rfl
  have hRE : refinedEulerian =
      ∑ σ : Equiv.Perm (Fin n),
        Polynomial.C (Polynomial.X ^ evenC n σ) *
          Polynomial.X ^ oddC n σ := by
    simp only [refinedEulerian, hodd, heven]
  have hPR : palindromicRefinement =
      (if n % 2 = 0 then Polynomial.C (1 + Polynomial.X) *
        (∑ σ : Equiv.Perm (Fin n),
          Polynomial.C (Polynomial.X ^ evenC n σ) *
            Polynomial.X ^ oddC n σ)
      else (∑ σ : Equiv.Perm (Fin n),
          Polynomial.C (Polynomial.X ^ evenC n σ) *
            Polynomial.X ^ oddC n σ)) := by
    simp only [palindromicRefinement, hRE]
  have hEval : ∀ p q : ℝ,
      Polynomial.eval q (Polynomial.eval (Polynomial.C p) palindromicRefinement) =
      (if n % 2 = 0 then (1 + q) else 1) *
        ∑ σ : Equiv.Perm (Fin n), p ^ oddC n σ * q ^ evenC n σ := by
    intro p q
    rw [hPR]
    by_cases h : n % 2 = 0
    · simp only [h, ite_true, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X, eval_refined]
    · simp only [h, ite_false, one_mul, eval_refined]
  have hNe : palindromicRefinement ≠ 0 := by
    intro h0
    have h1 : Polynomial.eval (1 : ℝ)
          (Polynomial.eval (Polynomial.C (1 : ℝ)) palindromicRefinement) =
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ) *
          (if n % 2 = 0 then 2 else 1) := by
      rw [hEval]
      simp only [one_pow, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      by_cases h : n % 2 = 0
      · simp only [h, ite_true]
        ring
      · simp only [h, ite_false]
        ring
    rw [h0] at h1
    simp only [Polynomial.eval_zero] at h1
    have hpos : (0 : ℝ) < (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
      have : 0 < Fintype.card (Equiv.Perm (Fin n)) := Fintype.card_pos
      exact Nat.cast_pos.mpr this
    have h2 : (0 : ℝ) < (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * (if n % 2 = 0 then 2 else 1) := by
      by_cases h : n % 2 = 0
      · simp only [h, ite_true]
        positivity
      · simp only [h, ite_false]
        positivity
    linarith
  refine ⟨hNe, ?_, ?_⟩
  · intro p q
    rw [hEval, hEval]
    by_cases h : n % 2 = 0
    · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 2 := ⟨n / 2 - 1, by omega⟩
      rw [ite_eq_left h, ite_eq_left h]
      exact Fp_even_symm m p q
    · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
      rw [ite_eq_right h, ite_eq_right h, one_mul, one_mul]
      have hR2 : (Fin.revPerm : Equiv.Perm (Fin (2 * m + 1))) * Fin.revPerm = 1 := by
        ext x
        simp only [Equiv.Perm.mul_apply, Fin.revPerm_apply, Equiv.Perm.one_apply, Fin.rev_rev]
      let R : Equiv.Perm (Fin (2 * m + 1)) := Fin.revPerm
      have hRR : R * R = 1 := hR2
      let e : Equiv.Perm (Fin (2 * m + 1)) ≃ Equiv.Perm (Fin (2 * m + 1)) :=
        { toFun := fun σ => R * σ * R
          invFun := fun σ => R * σ * R
          left_inv := by
            intro σ
            change R * (R * σ * R) * R = σ
            have hcalc : R * (R * σ * R) * R = (R * R) * σ * (R * R) := by group
            rw [hcalc, hRR, one_mul, mul_one]
          right_inv := by
            intro σ
            change R * (R * σ * R) * R = σ
            have hcalc : R * (R * σ * R) * R = (R * R) * σ * (R * R) := by group
            rw [hcalc, hRR, one_mul, mul_one] }
      have hE : (∑ σ : Equiv.Perm (Fin (2 * m + 1)),
            p ^ oddC (2 * m + 1) σ * q ^ evenC (2 * m + 1) σ)
          = (∑ σ : Equiv.Perm (Fin (2 * m + 1)),
            p ^ evenC (2 * m + 1) σ * q ^ oddC (2 * m + 1) σ) := by
        refine Fintype.sum_equiv e _ _ (fun σ => ?_)
        have h1 := (swap_of_rot_odd m σ).1
        have h2 := (swap_of_rot_odd m σ).2
        change p ^ oddC (2 * m + 1) σ * q ^ evenC (2 * m + 1) σ
            = p ^ evenC (2 * m + 1) (R * σ * R) * q ^ oddC (2 * m + 1) (R * σ * R)
        rw [h1, h2]
      rw [hE]
      apply Finset.sum_congr rfl
      intro σ _
      ring
  · intro p q hp hq
    rw [hEval, hEval]
    by_cases h : n % 2 = 0
    · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
      have hM : (2 * m) / 2 = m := by omega
      have hK : (2 * m - 1) / 2 = m - 1 := by omega
      rw [ite_eq_left h, ite_eq_left h, hM]
      let R : Equiv.Perm (Fin (2 * m)) := Fin.revPerm
      have hreidx : (∑ σ : Equiv.Perm (Fin (2 * m)),
            (p⁻¹) ^ oddC (2 * m) σ * (q⁻¹) ^ evenC (2 * m) σ)
          = (∑ σ : Equiv.Perm (Fin (2 * m)),
              (p⁻¹) ^ oddC (2 * m) (R * σ) * (q⁻¹) ^ evenC (2 * m) (R * σ)) :=
        (Fintype.sum_equiv (Equiv.mulLeft R) _ _ (fun σ => rfl)).symm
      calc (1 + q) * (∑ σ : Equiv.Perm (Fin (2 * m)), p ^ oddC (2 * m) σ * q ^ evenC (2 * m) σ)
          = ∑ σ : Equiv.Perm (Fin (2 * m)),
              (p * q) ^ m * ((1 + q⁻¹) *
                ((p⁻¹) ^ oddC (2 * m) (R * σ) * (q⁻¹) ^ evenC (2 * m) (R * σ))) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro σ _
            have hoC : oddC (2 * m) (R * σ) = m - oddC (2 * m) σ := by
              rw [show R * σ = Fin.revPerm * σ from rfl, odd_compl (2 * m) σ, hM]
            have heC : evenC (2 * m) (R * σ) = (m - 1) - evenC (2 * m) σ := by
              rw [show R * σ = Fin.revPerm * σ from rfl, even_compl (2 * m) σ, hK]
            rw [hoC, heC]
            have hle_o : oddC (2 * m) σ ≤ m := by
              have hh := oddC_le (2 * m) σ
              omega
            have hle_e : evenC (2 * m) σ + 1 ≤ m := by
              have hh := evenC_le (2 * m) σ
              omega
            have hpm : p ^ m = p ^ oddC (2 * m) σ * p ^ (m - oddC (2 * m) σ) := by
              rw [← pow_add, Nat.add_sub_cancel' hle_o]
            have hme : m - evenC (2 * m) σ = (m - 1 - evenC (2 * m) σ) + 1 := by omega
            have hqm : q ^ m = q ^ evenC (2 * m) σ * q ^ (m - evenC (2 * m) σ) := by
              have hle : evenC (2 * m) σ ≤ m := by omega
              rw [← pow_add, Nat.add_sub_cancel' hle]
            have hqm2 : q ^ (m - evenC (2 * m) σ) = q ^ (m - 1 - evenC (2 * m) σ) * q := by
              rw [hme, pow_add, pow_one]
            have hpo : p ^ (m - oddC (2 * m) σ) ≠ 0 := pow_ne_zero _ hp
            have hqo : q ^ (m - 1 - evenC (2 * m) σ) ≠ 0 := pow_ne_zero _ hq
            rw [mul_pow, inv_pow, inv_pow, hpm, hqm, hqm2]
            field_simp
            ring
        _ = (p * q) ^ m * ((1 + q⁻¹) *
              (∑ σ : Equiv.Perm (Fin (2 * m)),
                (p⁻¹) ^ oddC (2 * m) σ * (q⁻¹) ^ evenC (2 * m) σ)) := by
            rw [hreidx, ← Finset.mul_sum, ← Finset.mul_sum]
    · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
      have hM : (2 * m + 1) / 2 = m := by omega
      have hK : (2 * m + 1 - 1) / 2 = m := by omega
      rw [ite_eq_right h, ite_eq_right h, one_mul, one_mul, hM]
      let R : Equiv.Perm (Fin (2 * m + 1)) := Fin.revPerm
      have hreidx : (∑ σ : Equiv.Perm (Fin (2 * m + 1)),
            (p⁻¹) ^ oddC (2 * m + 1) σ * (q⁻¹) ^ evenC (2 * m + 1) σ)
          = (∑ σ : Equiv.Perm (Fin (2 * m + 1)),
              (p⁻¹) ^ oddC (2 * m + 1) (R * σ) * (q⁻¹) ^ evenC (2 * m + 1) (R * σ)) :=
        (Fintype.sum_equiv (Equiv.mulLeft R) _ _ (fun σ => rfl)).symm
      rw [hreidx, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      have hoC : oddC (2 * m + 1) (R * σ) = m - oddC (2 * m + 1) σ := by
        rw [show R * σ = Fin.revPerm * σ from rfl, odd_compl (2 * m + 1) σ, hM]
      have heC : evenC (2 * m + 1) (R * σ) = m - evenC (2 * m + 1) σ := by
        rw [show R * σ = Fin.revPerm * σ from rfl, even_compl (2 * m + 1) σ, hK]
      rw [hoC, heC]
      have hle_o : oddC (2 * m + 1) σ ≤ m := by
        have hh := oddC_le (2 * m + 1) σ
        omega
      have hle_e : evenC (2 * m + 1) σ ≤ m := by
        have hh := evenC_le (2 * m + 1) σ
        omega
      have hpm : p ^ m = p ^ oddC (2 * m + 1) σ * p ^ (m - oddC (2 * m + 1) σ) := by
        rw [← pow_add, Nat.add_sub_cancel' hle_o]
      have hqm : q ^ m = q ^ evenC (2 * m + 1) σ * q ^ (m - evenC (2 * m + 1) σ) := by
        rw [← pow_add, Nat.add_sub_cancel' hle_e]
      have hpo : p ^ (m - oddC (2 * m + 1) σ) ≠ 0 := pow_ne_zero _ hp
      have hqo : q ^ (m - evenC (2 * m + 1) σ) ≠ 0 := pow_ne_zero _ hq
      rw [mul_pow, inv_pow, inv_pow, hpm, hqm]
      field_simp

end MetaMathlibExt
end
