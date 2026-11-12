/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Real.Basic
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

import Mathlib.Tactic.Ring

@[expose] public section

namespace MathlibExt.Combinatorics.Coding.Plotkin

/-! # The Plotkin bound

A binary code of length `n` and minimum Hamming distance at least
`d`, with `n < 2d`, has at most `2d / (2d - n)` codewords. The proof
is the classical double count of the sum of pairwise distances.
This file covers roadmap package QCI-37 of the Atlas TCS canon
roadmap.

Source: M. Plotkin, "Binary codes with specified minimum distance",
IRE Transactions on Information Theory 6 (1960), 445--450.
-/

open Finset

private lemma card_filter_eq_sum_ite {α : Type*} (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (s.filter p).card = ∑ a ∈ s, if p a then 1 else 0 := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- The Plotkin bound: a binary code of length `n` and minimum
Hamming distance at least `d`, with `n < 2d`, has at most
`2d / (2d - n)` codewords. -/
theorem plotkin_bound {n d : ℕ} (hd : n < 2 * d)
    (C : Finset (Fin n → Fin 2))
    (hC : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y) :
    (C.card : ℝ) ≤ 2 * d / (2 * d - n) := by
  -- Unfold the canonical Hamming distance to the filtered-coordinate count
  -- used by the double-counting proof below.
  have hC' : ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
      d ≤ (Finset.univ.filter fun i => x i ≠ y i).card := by
    intro x hx y hy hne
    exact hC x hx y hy hne
  have hdenom_pos : (0:ℝ) < 2 * (d:ℝ) - (n:ℝ) := by
    have h : (n:ℝ) < 2 * (d:ℝ) := by exact_mod_cast hd
    linarith
  by_cases hM0 : C.card = 0
  · have hM' : (C.card : ℝ) = 0 := by simp [hM0]
    rw [hM']
    have hnum : (0:ℝ) ≤ 2 * (d:ℝ) := by positivity
    have hle : (0:ℝ) ≤ 2 * (d:ℝ) / (2 * (d:ℝ) - (n:ℝ)) :=
      div_nonneg hnum (le_of_lt hdenom_pos)
    convert hle using 2
  · have hM1 : 1 ≤ C.card := Nat.one_le_iff_ne_zero.mpr hM0
    have hMpos : (0:ℝ) < (C.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hM0
    have hLower_nat : C.card * (C.card - 1) * d
        ≤ ∑ x ∈ C, ∑ y ∈ C, (Finset.univ.filter fun i => x i ≠ y i).card := by
      have hper : ∀ x ∈ C, (C.card - 1) * d
          ≤ ∑ y ∈ C, (Finset.univ.filter fun i => x i ≠ y i).card := by
        intro x hx
        have hcard : (C.erase x).card = C.card - 1 := Finset.card_erase_of_mem hx
        have h1 : (C.erase x).card * d = ∑ y ∈ C.erase x, d := by
          rw [Finset.sum_const, smul_eq_mul]
        have h2 : ∑ y ∈ C.erase x, d
            ≤ ∑ y ∈ C.erase x, (Finset.univ.filter fun i => x i ≠ y i).card := by
          apply Finset.sum_le_sum
          intro y hy
          rw [Finset.mem_erase] at hy
          exact hC' x hx y hy.2 (Ne.symm hy.1)
        have h3 : ∑ y ∈ C.erase x, (Finset.univ.filter fun i => x i ≠ y i).card
            ≤ ∑ y ∈ C, (Finset.univ.filter fun i => x i ≠ y i).card := by
          apply Finset.sum_le_sum_of_subset
          exact Finset.erase_subset x C
        rw [hcard] at h1
        rw [h1]
        exact le_trans h2 h3
      have hsum : ∑ x ∈ C, ((C.card - 1) * d)
          ≤ ∑ x ∈ C, (∑ y ∈ C, (Finset.univ.filter fun i => x i ≠ y i).card) :=
        Finset.sum_le_sum hper
      have hconst : ∑ x ∈ C, ((C.card - 1) * d) = C.card * (C.card - 1) * d := by
        rw [Finset.sum_const, smul_eq_mul]
        ring
      rw [← hconst]
      exact hsum
    have hSwap : (∑ x ∈ C, ∑ y ∈ C, (Finset.univ.filter fun i => x i ≠ y i).card)
        = ∑ i ∈ Finset.univ, ∑ x ∈ C, ∑ y ∈ C, (if x i ≠ y i then 1 else 0) := by
      have hdist : ∀ x : Fin n → Fin 2, ∀ y : Fin n → Fin 2,
          (Finset.univ.filter fun i => x i ≠ y i).card
            = ∑ i ∈ Finset.univ, (if x i ≠ y i then 1 else 0) := by
        intro x y
        rw [card_filter_eq_sum_ite]
      calc ∑ x ∈ C, ∑ y ∈ C, (Finset.univ.filter fun i => x i ≠ y i).card
          = ∑ x ∈ C, ∑ y ∈ C, ∑ i ∈ Finset.univ, (if x i ≠ y i then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro x _
            apply Finset.sum_congr rfl
            intro y _
            exact hdist x y
        _ = ∑ x ∈ C, ∑ i ∈ Finset.univ, ∑ y ∈ C, (if x i ≠ y i then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro x _
            exact Finset.sum_comm
        _ = ∑ i ∈ Finset.univ, ∑ x ∈ C, ∑ y ∈ C, (if x i ≠ y i then 1 else 0) :=
            Finset.sum_comm
    have hCoord : ∀ i : Fin n, (∑ x ∈ C, ∑ y ∈ C, (if x i ≠ y i then 1 else 0))
        = 2 * (C.filter fun x => x i = 1).card
          * (C.card - (C.filter fun x => x i = 1).card) := by
      intro i
      set k := (C.filter fun x => x i = 1).card with hk
      set M := C.card with hM
      have hcompl : (C.filter fun x => ¬ x i = 1).card = M - k := by
        have h := Finset.card_filter_add_card_filter_not (s := C) (fun x => x i = 1)
        simp only [hM, hk] at h ⊢
        omega
      have hinner : ∀ x ∈ C, (∑ y ∈ C, (if x i ≠ y i then 1 else 0))
          = (if x i = 1 then M - k else k) := by
        intro x hx
        by_cases hxi : x i = 1
        · have heq : ∀ y ∈ C, (if x i ≠ y i then (1:ℕ) else 0)
              = (if y i ≠ 1 then 1 else 0) := by
            intro y _
            rw [hxi]
            by_cases hyi : y i = 1 <;> simp [hyi, eq_comm]
          rw [Finset.sum_congr rfl heq]
          have hcard : (∑ y ∈ C, (if y i ≠ 1 then (1:ℕ) else 0))
              = (C.filter fun y => y i ≠ 1).card := by
            rw [card_filter_eq_sum_ite]
          rw [hcard]
          have hsame : (C.filter fun y => y i ≠ 1) = C.filter fun y => ¬ y i = 1 := rfl
          rw [hsame, hcompl]
          simp [hxi]
        · have hx0 : x i = 0 := by omega
          have heq : ∀ y ∈ C, (if x i ≠ y i then (1:ℕ) else 0)
              = (if y i = 1 then 1 else 0) := by
            intro y _
            rw [hx0]
            by_cases hyi : y i = 1
            · simp [hyi]
            · have hy0 : y i = 0 := by omega
              simp [hy0]
          rw [Finset.sum_congr rfl heq]
          have hcard : (∑ y ∈ C, (if y i = 1 then (1:ℕ) else 0))
              = (C.filter fun y => y i = 1).card := by
            rw [card_filter_eq_sum_ite]
          rw [hcard, ← hk]
          simp [hxi]
      calc ∑ x ∈ C, ∑ y ∈ C, (if x i ≠ y i then 1 else 0)
          = ∑ x ∈ C, (if x i = 1 then M - k else k) := Finset.sum_congr rfl hinner
        _ = ∑ x ∈ C.filter (fun x => x i = 1), (M - k)
              + ∑ x ∈ C.filter (fun x => ¬ x i = 1), k := by
            have hsplit := Finset.sum_filter_add_sum_filter_not C (fun x => x i = 1)
              (fun x => if x i = 1 then M - k else k)
            have h1 : ∑ x ∈ C.filter (fun x => x i = 1),
                  (if x i = 1 then M - k else k)
                = ∑ x ∈ C.filter (fun x => x i = 1), (M - k) := by
              apply Finset.sum_congr rfl
              intro x hxmem
              rw [Finset.mem_filter] at hxmem
              simp [hxmem.2]
            have h2 : ∑ x ∈ C.filter (fun x => ¬ x i = 1),
                  (if x i = 1 then M - k else k)
                = ∑ x ∈ C.filter (fun x => ¬ x i = 1), k := by
              apply Finset.sum_congr rfl
              intro x hxmem
              rw [Finset.mem_filter] at hxmem
              simp [hxmem.2]
            rw [h1, h2] at hsplit
            rw [← hsplit]
        _ = k * (M - k) + (M - k) * k := by
            rw [Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, hk, hcompl]
        _ = 2 * k * (M - k) := by ring
        _ = 2 * (C.filter fun x => x i = 1).card
              * (C.card - (C.filter fun x => x i = 1).card) := by
            simp [hM, hk]
    have hS_eq : (∑ x ∈ C, ∑ y ∈ C, (Finset.univ.filter fun i => x i ≠ y i).card)
        = ∑ i ∈ Finset.univ, (2 * (C.filter fun x => x i = 1).card
          * (C.card - (C.filter fun x => x i = 1).card)) := by
      rw [hSwap]
      apply Finset.sum_congr rfl
      intro i _
      exact hCoord i
    have hLower_real : (C.card : ℝ) * ((C.card : ℝ) - 1) * (d : ℝ)
        ≤ ((∑ x ∈ C, ∑ y ∈ C, (Finset.univ.filter fun i => x i ≠ y i).card : ℕ) : ℝ) := by
      have hsub : (((C.card - 1 : ℕ)) : ℝ) = (C.card : ℝ) - 1 := by
        rw [Nat.cast_sub hM1, Nat.cast_one]
      have heq : (((C.card * (C.card - 1) * d : ℕ)) : ℝ)
          = (C.card : ℝ) * ((C.card : ℝ) - 1) * (d : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_mul, hsub]
      rw [← heq]
      exact Nat.cast_le.mpr hLower_nat
    have hUpper_real : ((∑ x ∈ C, ∑ y ∈ C,
          (Finset.univ.filter fun i => x i ≠ y i).card : ℕ) : ℝ)
        ≤ (n : ℝ) * (C.card : ℝ)^2 / 2 := by
      rw [hS_eq, Nat.cast_sum]
      have hper : ∀ i ∈ Finset.univ,
          (((2 * (C.filter fun x => x i = 1).card
            * (C.card - (C.filter fun x => x i = 1).card) : ℕ)) : ℝ)
            ≤ (C.card : ℝ)^2 / 2 := by
        intro i _
        set k := (C.filter fun x => x i = 1).card with hk
        set M := C.card with hM
        have hkle : k ≤ M := by
          simp only [hk, hM]
          exact Finset.card_filter_le C _
        have hsub : ((M - k : ℕ) : ℝ) = (M : ℝ) - (k : ℝ) := Nat.cast_sub hkle
        push_cast
        rw [hsub]
        nlinarith [sq_nonneg ((M : ℝ) - 2 * (k : ℝ))]
      have hle : ∑ i ∈ Finset.univ,
            (((2 * (C.filter fun x => x i = 1).card
              * (C.card - (C.filter fun x => x i = 1).card) : ℕ)) : ℝ)
          ≤ ∑ i ∈ Finset.univ, ((C.card : ℝ)^2 / 2) :=
        Finset.sum_le_sum hper
      have hconst : ∑ i ∈ (Finset.univ : Finset (Fin n)), ((C.card : ℝ)^2 / 2)
          = (n : ℝ) * (C.card : ℝ)^2 / 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      rw [← hconst]
      exact hle
    have hle : (C.card : ℝ) * ((C.card : ℝ) - 1) * (d : ℝ)
        ≤ (n : ℝ) * (C.card : ℝ)^2 / 2 :=
      le_trans hLower_real hUpper_real
    have hdiv : ((C.card : ℝ) - 1) * (d : ℝ) ≤ (n : ℝ) * (C.card : ℝ) / 2 := by
      have hle2 : (C.card : ℝ) * (((C.card : ℝ) - 1) * (d : ℝ))
          ≤ (C.card : ℝ) * ((n : ℝ) * (C.card : ℝ) / 2) := by
        ring_nf at hle ⊢
        exact hle
      exact le_of_mul_le_mul_left hle2 hMpos
    have hfinal : (C.card : ℝ) * (2 * (d : ℝ) - (n : ℝ)) ≤ 2 * (d : ℝ) := by
      linarith
    rw [le_div_iff₀ hdenom_pos]
    convert hfinal using 2

end MathlibExt.Combinatorics.Coding.Plotkin
