/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.ChuMSTDFamilies
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

open Pointwise

private def offset (d l p : ℕ) : ℕ :=
  if p < 2 * l then d * (p / 2 + 1) + 1 + p % 2 else d * l + 3

private theorem offset_bounds {d l p : ℕ} (hd : 2 ≤ d) :
    3 ≤ offset d l p ∧ offset d l p ≤ d * l + 3 := by
  have hr := Nat.mod_lt p (by omega : 0 < 2)
  have he := Nat.mod_add_div p 2
  dsimp [offset]
  split_ifs with h
  · have hq : p / 2 + 1 ≤ l := by omega
    constructor <;> nlinarith
  · constructor <;> nlinarith

private theorem offset_inj {d l p q : ℕ} (hd : 2 ≤ d)
    (hp : p < 2 * l + 1) (hq : q < 2 * l + 1)
    (he : offset d l p = offset d l q) : p = q := by
  have hrp := Nat.mod_lt p (by omega : 0 < 2)
  have hrq := Nat.mod_lt q (by omega : 0 < 2)
  have hep := Nat.mod_add_div p 2
  have heq := Nat.mod_add_div q 2
  dsimp [offset] at he
  split_ifs at he with h₁ h₂
  · have hdiv : p / 2 = q / 2 := by
      by_contra hn
      rcases lt_or_gt_of_ne hn with h | h
      · have hmul := Nat.mul_le_mul_left d (show p / 2 + 1 ≤ q / 2 by omega)
        simp only [Nat.mul_add, Nat.mul_one] at he hmul
        omega
      · have hmul := Nat.mul_le_mul_left d (show q / 2 + 1 ≤ p / 2 by omega)
        simp only [Nat.mul_add, Nat.mul_one] at he hmul
        omega
    have hmod : p % 2 = q % 2 := by rw [hdiv] at he; omega
    omega
  · have h : p / 2 + 1 ≤ l := by omega
    have hm := Nat.mul_le_mul_left d h
    omega
  · have h : q / 2 + 1 ≤ l := by omega
    have hm := Nat.mul_le_mul_left d h
    omega
  · omega

private theorem grid_inj {d l : ℕ} (hd : 2 ≤ d)
    {a b : ℕ × ℕ} (ha : a.2 < 2 * l + 1) (hb : b.2 < 2 * l + 1)
    (he : (d * l + 1) * a.1 + offset d l a.2 =
      (d * l + 1) * b.1 + offset d l b.2) : a = b := by
  have hA := offset_bounds (l := l) (p := a.2) hd
  have hB := offset_bounds (l := l) (p := b.2) hd
  have hfirst : a.1 = b.1 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · have hmul := Nat.mul_le_mul_left (d * l + 1) (show a.1 + 1 ≤ b.1 by omega)
      simp only [Nat.mul_add, Nat.mul_one] at hmul
      omega
    · have hmul := Nat.mul_le_mul_left (d * l + 1) (show b.1 + 1 ≤ a.1 by omega)
      simp only [Nat.mul_add, Nat.mul_one] at hmul
      omega
  have hsecond : a.2 = b.2 := offset_inj hd ha hb (by rw [hfirst] at he; omega)
  exact Prod.ext hfirst hsecond

private theorem block_point {k l t : ℕ} (hk : 0 < k) (hl : 0 < l) (ht : 0 < t)
    (i j : ℕ) (hi : i ≤ l) (hj : j < t) :
    ((4 * (((k + 1) * l + 1) * j + (k + 1) * i + 1) : ℕ) : ℤ) ∈
      chuFamilyKLT k l t := by
  convert chuFamilyKLT_mem_block_starts hk hl ht i j hi hj using 1
  push_cast
  ring

private theorem boundary_point {k l t : ℕ} (hk : 0 < k) (hl : 0 < l) (ht : 0 < t)
    (j : ℕ) (hj : j ≤ t) :
    ((4 * (((k + 1) * l + 1) * j) : ℕ) : ℤ) ∈ chuFamilyKLT k l t := by
  cases j with
  | zero =>
    simp only [Nat.mul_zero, Int.natCast_zero]
    cases t <;> simp [chuFamilyKLT, List.replicate_succ, List.flatten_cons,
      List.append_assoc, setOfConsecutiveDifferences_cons]
  | succ j =>
    convert block_point hk hl ht l j le_rfl (by omega) using 1

private theorem head_point {k l t : ℕ} (hk : 0 < k) (hl : 0 < l) (ht : 0 < t)
    (j : ℕ) (hj : j ≤ t) :
    ((4 * (((k + 1) * l + 1) * j + 1) : ℕ) : ℤ) ∈ chuFamilyKLT k l t := by
  by_cases h : j < t
  · simpa using block_point hk hl ht 0 j (by omega) h
  · have hje : j = t := by omega
    subst j
    convert (chuFamilyKLT_mem hk hl ht).2.2 using 1
    push_cast
    ring

private theorem split_index {t q : ℕ} (hq : q < 2 * t) :
    ∃ a b : ℕ, a ≤ t ∧ b < t ∧ a + b = q := by
  refine ⟨min q t, q - min q t, ?_, ?_, ?_⟩ <;> omega

private theorem zero_grid_mem {k l t q p : ℕ} (hk : 0 < k) (hl : 0 < l)
    (ht : 0 < t) (hq : q < 2 * t) :
    ((4 * ((((k + 1) * l + 1) * q) +
      (if p < 2 * l then (k + 1) * (p / 2 + 1) + 1 + p % 2
        else (k + 1) * l + 3)) : ℕ) : ℤ) ∈
      chuFamilyKLT k l t + chuFamilyKLT k l t := by
  have hrem := Nat.mod_lt p (by omega : 0 < 2)
  have hdiv := Nat.mod_add_div p 2
  obtain ⟨a, b, ha, hb, hab⟩ := split_index hq
  split_ifs with h
  · have hi : p / 2 + 1 ≤ l := by omega
    have hs := block_point hk hl ht (p / 2 + 1) b hi hb
    have hm : p % 2 = 0 ∨ p % 2 = 1 := by omega
    rcases hm with hm | hm
    · convert Finset.add_mem_add (boundary_point hk hl ht a ha) hs using 1
      norm_cast
      rw [hm, ← hab]
      ring
    · convert Finset.add_mem_add (head_point hk hl ht a ha) hs using 1
      norm_cast
      rw [hm, ← hab]
      ring
  · have hnext : q + 1 ≤ 2 * t := by omega
    let a := min (q + 1) t
    let b := q + 1 - a
    have ha : a ≤ t := by dsimp [a]; omega
    have hb : b ≤ t := by dsimp [a, b]; omega
    have hab : a + b = q + 1 := by dsimp [a, b]; omega
    convert Finset.add_mem_add (head_point hk hl ht a ha) (head_point hk hl ht b hb)
      using 1
    norm_cast
    convert congrArg (fun x : ℕ => 4 * (((k + 1) * l + 1) * x + 2)) hab.symm
      using 1
    ring

/-- **Lower bound for the sumset of the Chu family set.** Let $k$, $l$, $t$ be positive integers
and let $A \subseteq \mathbb{Z}$ be the Chu family set with parameters $k$, $l$, $t$. Then
$|A + A| \ge 11 + 6klt + 10lt + 8t$.

Together with $|A - A| = 11 + 6klt + 8lt + 8t$ (Theorem 6), this shows that $A$ is sum-dominated
(MSTD): $|A + A| > |A - A|$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Theorem 7 (`integers-2024-A32-thm-7`). -/
public theorem chuFamilyKLT_card_add {k l t : ℕ} (hk : 0 < k) (hl : 0 < l) (ht : 0 < t) :
    11 + 6 * k * l * t + 10 * l * t + 8 * t ≤ (chuFamilyKLT k l t + chuFamilyKLT k l t).card := by
  classical
  let T := t * (k * l + l + 1)
  let Z := Fin 3 ⊕ (Fin (2 * t) × Fin (2 * l + 1))
  let R := (Fin (2 * T + 3) × Fin 2) ⊕ Fin (2 * T + 2)
  let z : Z → ℕ := Sum.elim Fin.val (fun p =>
    ((k + 1) * l + 1) * p.1.val + offset (k + 1) l p.2.val)
  have hz : Function.Injective z := by
    apply Function.Injective.sumElim Fin.val_injective
    · intro a b h
      dsimp only at h
      have hh := grid_inj (l := l) (a := (a.1.val, a.2.val)) (b := (b.1.val, b.2.val))
        (by omega : 2 ≤ k + 1) a.2.isLt b.2.isLt h
      exact Prod.ext (Fin.ext (congrArg Prod.fst hh)) (Fin.ext (congrArg Prod.snd hh))
    · intro a b h
      have ha := a.isLt
      have hb := offset_bounds (l := l) (p := b.2.val) (by omega : 2 ≤ k + 1)
      omega
  let r : R → ℕ := Sum.elim (fun p => p.2.val + 1 + 4 * p.1.val)
    (fun i => 3 + 4 * i.val)
  have hr : Function.Injective r := by
    apply Function.Injective.sumElim
    · intro a b h
      dsimp only at h
      have ha := a.2.isLt
      have hb := b.2.isLt
      exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
    · intro a b h
      dsimp only at h
      exact Fin.ext (by omega)
    · intro a b h
      have ha := a.2.isLt
      omega
  let f : Z ⊕ R → ℕ := Sum.elim (fun i => 4 * z i) r
  have hf : Function.Injective f := by
    apply Function.Injective.sumElim
    · intro a b h
      dsimp only at h
      exact hz (by omega)
    · exact hr
    · intro a b h
      cases b with
      | inl b =>
        have hb := b.2.isLt
        change 4 * z a = b.2.val + 1 + 4 * b.1.val at h
        omega
      | inr b =>
        change 4 * z a = 3 + 4 * b.val at h
        omega
  have hmem (i : Z ⊕ R) : (f i : ℤ) ∈ chuFamilyKLT k l t + chuFamilyKLT k l t := by
    cases i with
    | inl i =>
      cases i with
      | inl i =>
        have hzero := boundary_point hk hl ht 0 (by omega)
        have hfour := head_point hk hl ht 0 (by omega)
        fin_cases i
        · simpa [f, z] using Finset.add_mem_add hzero hzero
        · simpa [f, z] using Finset.add_mem_add hzero hfour
        · simpa [f, z] using Finset.add_mem_add hfour hfour
      | inr i => exact zero_grid_mem hk hl ht i.1.isLt
    | inr i =>
      obtain ⟨h₁₂, h₃⟩ := chuFamilyKLT_mem_add hk hl ht
      cases i with
      | inl p =>
        have hi : p.1.val ≤ 2 + 2 * (t * (k * l + l + 1)) := by
          have h := p.1.isLt
          dsimp [T] at h
          omega
        rcases p with ⟨i, j⟩
        fin_cases j
        · simpa [f, r] using (h₁₂ i.val hi).1
        · simpa [f, r] using (h₁₂ i.val hi).2
      | inr i =>
        have hi : i.val ≤ 1 + 2 * (t * (k * l + l + 1)) := by
          have h := i.isLt
          dsimp [T] at h
          omega
        simpa [f, r] using h₃ i.val hi
  let g : Z ⊕ R → ↥(chuFamilyKLT k l t + chuFamilyKLT k l t) :=
    fun i => ⟨(f i : ℤ), hmem i⟩
  have hg : Function.Injective g := by
    intro a b h
    apply hf
    have hh : (f a : ℤ) = (f b : ℤ) := congrArg Subtype.val h
    exact_mod_cast hh
  have hcard := Fintype.card_le_of_injective g hg
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe,
    Z, R] at hcard
  dsimp [T] at hcard
  nlinarith

end MetaMathlibExt
