/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

@[expose] public section



private theorem filter_ne_eq_erase {α : Type*} [DecidableEq α] (s : Finset α) (a : α) :
    s.filter (fun x => a ≠ x) = s.erase a := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_erase]
  exact ⟨fun h => ⟨Ne.symm h.2, h.1⟩, fun h => ⟨h.2, Ne.symm h.1⟩⟩

private theorem sum_ite_ne_const {α : Type*} [DecidableEq α] (s : Finset α) (a : α) (c : ℝ) :
    (∑ x ∈ s, (if a ≠ x then c else 0)) = ((s.erase a).card : ℝ) * c := by
  have h : (∑ x ∈ s.filter (fun x => a ≠ x), c)
      = ∑ x ∈ s, (if a ≠ x then c else 0) :=
    Finset.sum_filter _ _
  rw [← h, filter_ne_eq_erase, Finset.sum_const, nsmul_eq_mul]

/-- FKS perfect hashing, level-1 existence: for a universal hash
family into `|K|²` buckets, some member of the family has total
collision count (summed over buckets, `len * (len - 1)` counting
ordered distinct colliding pairs) below `|K|`: rehashing each
bucket with its own quadratic table then gives a linear-space
perfect hash. Universality: for distinct keys, the number of
family members colliding them is at most `|H| / |K|²`. -/
theorem fks_exists_good_hash {K H : Type*} [Fintype K] [Fintype H]
    (hash : H → K → Fin (Fintype.card K ^ 2))
    (huniv : ∀ x y : K, x ≠ y →
      ((Finset.univ.filter (fun hh => hash hh x = hash hh y)).card : ℝ) ≤
        (Fintype.card H : ℝ) / (Fintype.card K : ℝ) ^ 2)
    (hK : 0 < Fintype.card K) (hH : 0 < Fintype.card H) :
    ∃ hh : H, (∑ b : Fin (Fintype.card K ^ 2),
        ((Finset.univ.filter (fun y => hash hh y = b)).card : ℝ) *
          ((Finset.univ.filter (fun y => hash hh y = b)).card - 1)) <
      (Fintype.card K : ℝ) := by
  classical
  have step1 : ∀ hh : H, (∑ b : Fin (Fintype.card K ^ 2),
      ((Finset.univ.filter (fun y => hash hh y = b)).card : ℝ) *
        ((Finset.univ.filter (fun y => hash hh y = b)).card - 1))
      = ∑ y : K, ∑ z : K, (if y ≠ z ∧ hash hh y = hash hh z then (1:ℝ) else 0) := by
    intro hh
    have perBucket : ∀ b : Fin (Fintype.card K ^ 2),
        ((Finset.univ.filter (fun y => hash hh y = b)).card : ℝ) *
          ((Finset.univ.filter (fun y => hash hh y = b)).card - 1)
        = ∑ y ∈ Finset.univ.filter (fun y => hash hh y = b),
          ∑ z ∈ Finset.univ.filter (fun y => hash hh y = b),
            (if y ≠ z then (1:ℝ) else 0) := by
      intro b
      have hinner : ∀ y ∈ Finset.univ.filter (fun y => hash hh y = b),
          (∑ z ∈ Finset.univ.filter (fun y => hash hh y = b),
            (if y ≠ z then (1:ℝ) else 0))
          = ((Finset.univ.filter (fun y => hash hh y = b)).card : ℝ) - 1 := by
        intro y hy
        have hpos : 0 < (Finset.univ.filter (fun y => hash hh y = b)).card :=
          Finset.card_pos.mpr ⟨y, hy⟩
        have h1 : (∑ z ∈ Finset.univ.filter (fun y => hash hh y = b),
            (if y ≠ z then (1:ℝ) else 0))
            = (((Finset.univ.filter (fun y => hash hh y = b)).erase y).card : ℝ) * 1 :=
          sum_ite_ne_const _ y 1
        have h3 : ((Finset.univ.filter (fun y => hash hh y = b)).erase y).card
            = (Finset.univ.filter (fun y => hash hh y = b)).card - 1 :=
          Finset.card_erase_of_mem hy
        rw [h1, h3,
          Nat.cast_sub (show 1 ≤ (Finset.univ.filter (fun y => hash hh y = b)).card from hpos)]
        simp
      have hsum : (∑ y ∈ Finset.univ.filter (fun y => hash hh y = b),
          ∑ z ∈ Finset.univ.filter (fun y => hash hh y = b),
            (if y ≠ z then (1:ℝ) else 0))
          = ∑ y ∈ Finset.univ.filter (fun y => hash hh y = b),
            (((Finset.univ.filter (fun y => hash hh y = b)).card : ℝ) - 1) :=
        Finset.sum_congr rfl (fun y hy => hinner y hy)
      rw [hsum, Finset.sum_const, nsmul_eq_mul]
    have perY : ∀ y : K, (∑ z : K,
        (if y ≠ z ∧ hash hh y = hash hh z then (1:ℝ) else 0))
        = ∑ z ∈ Finset.univ.filter (fun z => hash hh z = hash hh y),
          (if y ≠ z then (1:ℝ) else 0) := by
      intro y
      have h : (∑ z ∈ Finset.univ.filter (fun z => hash hh z = hash hh y),
          (if y ≠ z then (1:ℝ) else 0))
          = ∑ z ∈ Finset.univ,
            (if hash hh z = hash hh y then (if y ≠ z then (1:ℝ) else 0) else 0) :=
        Finset.sum_filter _ _
      rw [h]
      apply Finset.sum_congr rfl
      intro z _
      simp only [eq_comm (a := hash hh z) (b := hash hh y)]
      by_cases hyz : y ≠ z <;> by_cases hcoll : hash hh y = hash hh z <;>
        simp [hyz, hcoll]
    have hcollapse : ∀ b : Fin (Fintype.card K ^ 2),
        (∑ y ∈ Finset.univ.filter (fun y => hash hh y = b),
          ∑ z ∈ Finset.univ.filter (fun y => hash hh y = b),
            (if y ≠ z then (1:ℝ) else 0))
        = ∑ y ∈ Finset.univ.filter (fun y => hash hh y = b),
          (∑ z : K, (if y ≠ z ∧ hash hh y = hash hh z then (1:ℝ) else 0)) := by
      intro b
      apply Finset.sum_congr rfl
      intro y hy
      have hy' : hash hh y = b := by simpa using hy
      rw [perY y]
      have hBB : Finset.univ.filter (fun z => hash hh z = b)
          = Finset.univ.filter (fun z => hash hh z = hash hh y) := by rw [hy']
      rw [hBB]
    calc (∑ b : Fin (Fintype.card K ^ 2),
          ((Finset.univ.filter (fun y => hash hh y = b)).card : ℝ) *
            ((Finset.univ.filter (fun y => hash hh y = b)).card - 1))
          = ∑ b : Fin (Fintype.card K ^ 2),
            ∑ y ∈ Finset.univ.filter (fun y => hash hh y = b),
              ∑ z ∈ Finset.univ.filter (fun y => hash hh y = b),
                (if y ≠ z then (1:ℝ) else 0) :=
            Finset.sum_congr rfl (fun b _ => perBucket b)
      _ = ∑ b : Fin (Fintype.card K ^ 2),
            ∑ y ∈ Finset.univ.filter (fun y => hash hh y = b),
              (∑ z : K, (if y ≠ z ∧ hash hh y = hash hh z then (1:ℝ) else 0)) :=
            Finset.sum_congr rfl (fun b _ => hcollapse b)
      _ = ∑ y : K, ∑ z : K,
            (if y ≠ z ∧ hash hh y = hash hh z then (1:ℝ) else 0) :=
            Finset.sum_fiberwise _ _ _
  have step2 : (∑ hh : H, ∑ y : K, ∑ z : K,
      (if y ≠ z ∧ hash hh y = hash hh z then (1:ℝ) else 0))
      = ∑ y : K, ∑ z : K, (if y ≠ z then
        ((Finset.univ.filter (fun hh => hash hh y = hash hh z)).card : ℝ) else 0) := by
    have hswap : (∑ hh : H, ∑ y : K, ∑ z : K,
        (if y ≠ z ∧ hash hh y = hash hh z then (1:ℝ) else 0))
        = ∑ y : K, ∑ z : K, ∑ hh : H,
          (if y ≠ z ∧ hash hh y = hash hh z then (1:ℝ) else 0) := by
      trans ∑ y : K, ∑ hh : H, ∑ z : K,
        (if y ≠ z ∧ hash hh y = hash hh z then (1:ℝ) else 0)
      · exact Finset.sum_comm
      · exact Finset.sum_congr rfl (fun y _ => Finset.sum_comm)
    rw [hswap]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro z _
    by_cases hyz : y ≠ z
    · have hterm : ∀ hh : H, (if y ≠ z ∧ hash hh y = hash hh z then (1:ℝ) else 0)
          = (if hash hh y = hash hh z then (1:ℝ) else 0) := by
        intro hh
        simp [hyz]
      trans ∑ hh : H, (if hash hh y = hash hh z then (1:ℝ) else 0)
      · exact Finset.sum_congr rfl (fun hh _ => hterm hh)
      · have hbool : (∑ hh : H, (if hash hh y = hash hh z then (1:ℝ) else 0))
            = ((Finset.univ.filter (fun hh => hash hh y = hash hh z)).card : ℝ) :=
          Finset.sum_boole _ _
        rw [hbool]
        simp [hyz]
    · simp [hyz]
  have hle : (∑ y : K, ∑ z : K, (if y ≠ z then
      ((Finset.univ.filter (fun hh => hash hh y = hash hh z)).card : ℝ) else 0))
      ≤ ∑ y : K, ∑ z : K, (if y ≠ z then
        (Fintype.card H : ℝ) / (Fintype.card K : ℝ) ^ 2 else 0) := by
    apply Finset.sum_le_sum
    intro y _
    apply Finset.sum_le_sum
    intro z _
    by_cases hyz : y ≠ z
    · simp only [ite_eq_left hyz]
      exact huniv y z hyz
    · simp [hyz]
  have hRHS : (∑ y : K, ∑ z : K, (if y ≠ z then
      (Fintype.card H : ℝ) / (Fintype.card K : ℝ) ^ 2 else 0))
      = (Fintype.card K : ℝ) * ((Fintype.card K : ℝ) - 1) *
        ((Fintype.card H : ℝ) / (Fintype.card K : ℝ) ^ 2) := by
    have hinner : ∀ y : K, (∑ z : K, (if y ≠ z then
        (Fintype.card H : ℝ) / (Fintype.card K : ℝ) ^ 2 else 0))
        = ((Fintype.card K : ℝ) - 1) *
          ((Fintype.card H : ℝ) / (Fintype.card K : ℝ) ^ 2) := by
      intro y
      have h1 : (∑ z : K, (if y ≠ z then
          (Fintype.card H : ℝ) / (Fintype.card K : ℝ) ^ 2 else 0))
          = (((Finset.univ.erase y).card : ℝ)) *
            ((Fintype.card H : ℝ) / (Fintype.card K : ℝ) ^ 2) :=
        sum_ite_ne_const _ y _
      have h3 : (Finset.univ.erase y).card = Fintype.card K - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ y), Finset.card_univ]
      rw [h1, h3, Nat.cast_sub (show 1 ≤ Fintype.card K from hK)]
      simp
    calc (∑ y : K, ∑ z : K, (if y ≠ z then
            (Fintype.card H : ℝ) / (Fintype.card K : ℝ) ^ 2 else 0))
          = ∑ y : K, (((Fintype.card K : ℝ) - 1) *
            ((Fintype.card H : ℝ) / (Fintype.card K : ℝ) ^ 2)) :=
            Finset.sum_congr rfl (fun y _ => hinner y)
      _ = (Fintype.card K : ℝ) * ((Fintype.card K : ℝ) - 1) *
            ((Fintype.card H : ℝ) / (Fintype.card K : ℝ) ^ 2) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
  have hlt : (Fintype.card K : ℝ) * ((Fintype.card K : ℝ) - 1) *
      ((Fintype.card H : ℝ) / (Fintype.card K : ℝ) ^ 2)
      < (Fintype.card H : ℝ) := by
    have hnR : (0:ℝ) < (Fintype.card K : ℝ) := by exact_mod_cast hK
    have hmR : (0:ℝ) < (Fintype.card H : ℝ) := by exact_mod_cast hH
    have hn_ne : (Fintype.card K : ℝ) ≠ 0 := ne_of_gt hnR
    have hfrac : ((Fintype.card K : ℝ) - 1) / (Fintype.card K : ℝ) < 1 := by
      rw [div_lt_one hnR]
      linarith
    have heq : (Fintype.card K : ℝ) * ((Fintype.card K : ℝ) - 1) *
        ((Fintype.card H : ℝ) / (Fintype.card K : ℝ) ^ 2)
        = (Fintype.card H : ℝ) * (((Fintype.card K : ℝ) - 1) / (Fintype.card K : ℝ)) := by
      field_simp
    rw [heq]
    have hmul := mul_lt_mul_of_pos_left hfrac hmR
    simpa using hmul
  have hlt' : (∑ y : K, ∑ z : K, (if y ≠ z then
      (Fintype.card H : ℝ) / (Fintype.card K : ℝ) ^ 2 else 0))
      < (Fintype.card H : ℝ) := by
    rw [hRHS]
    exact hlt
  have hDlt : (∑ hh : H, ∑ y : K, ∑ z : K,
      (if y ≠ z ∧ hash hh y = hash hh z then (1:ℝ) else 0))
      < (Fintype.card H : ℝ) := by
    rw [step2]
    exact lt_of_le_of_lt hle hlt'
  have htot : (∑ hh : H, ∑ b : Fin (Fintype.card K ^ 2),
      ((Finset.univ.filter (fun y => hash hh y = b)).card : ℝ) *
        ((Finset.univ.filter (fun y => hash hh y = b)).card - 1))
      < (Fintype.card H : ℝ) := by
    have hcongr : (∑ hh : H, ∑ b : Fin (Fintype.card K ^ 2),
        ((Finset.univ.filter (fun y => hash hh y = b)).card : ℝ) *
          ((Finset.univ.filter (fun y => hash hh y = b)).card - 1))
        = ∑ hh : H, ∑ y : K, ∑ z : K,
          (if y ≠ z ∧ hash hh y = hash hh z then (1:ℝ) else 0) :=
      Finset.sum_congr rfl (fun hh _ => step1 hh)
    rw [hcongr]
    exact hDlt
  have hn1 : (1:ℝ) ≤ (Fintype.card K : ℝ) := by exact_mod_cast hK
  have hmR : (0:ℝ) < (Fintype.card H : ℝ) := by exact_mod_cast hH
  have hcardH : (∑ _hh : H, (Fintype.card K : ℝ))
      = (Fintype.card H : ℝ) * (Fintype.card K : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hmn : (Fintype.card H : ℝ) ≤ (Fintype.card H : ℝ) * (Fintype.card K : ℝ) := by
    have hle1 := mul_le_mul_of_nonneg_left hn1 (le_of_lt hmR)
    simpa using hle1
  have hlt2 : (∑ hh : H, ∑ b : Fin (Fintype.card K ^ 2),
      ((Finset.univ.filter (fun y => hash hh y = b)).card : ℝ) *
        ((Finset.univ.filter (fun y => hash hh y = b)).card - 1))
      < ∑ _hh : H, (Fintype.card K : ℝ) := by
    rw [hcardH]
    exact lt_of_lt_of_le htot hmn
  obtain ⟨hh, _, hlt⟩ := Finset.exists_lt_of_sum_lt hlt2
  exact ⟨hh, hlt⟩
