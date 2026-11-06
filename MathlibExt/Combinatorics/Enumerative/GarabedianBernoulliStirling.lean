/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.NumberTheory.Bernoulli
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators

namespace MetaMathlibExt

section




private theorem aux_stirling (m t : ℕ) :
    ∑ i ∈ Finset.range (m + 1), (m.choose i : ℚ) * (-1 : ℚ) ^ i *
      (Nat.stirlingSecond (i + 1) (t + 1) : ℚ)
      = (-1 : ℚ) ^ m * (Nat.stirlingSecond m t : ℚ) := by
  induction m generalizing t with
  | zero =>
    rw [Finset.sum_range_one]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, pow_zero, Nat.zero_add]
    cases t with
    | zero =>
      rw [Nat.stirlingSecond_self, Nat.stirlingSecond_zero]
    | succ t =>
      have h : (1 : ℕ) < t + 1 + 1 := by omega
      rw [Nat.stirlingSecond_eq_zero_of_lt h, Nat.stirlingSecond_zero_succ]
  | succ m ih =>
    have pascal : ∀ i : ℕ, ((m + 1).choose (i + 1) : ℚ)
        = (m.choose i : ℚ) + (m.choose (i + 1) : ℚ) := by
      intro i
      have h := Nat.choose_succ_succ m i
      exact_mod_cast h
    have hS2 : ∀ (t i : ℕ), (Nat.stirlingSecond (i + 1 + 1) (t + 1) : ℚ)
        = ((t : ℚ) + 1) * (Nat.stirlingSecond (i + 1) (t + 1) : ℚ) +
          (Nat.stirlingSecond (i + 1) t : ℚ) := by
      intro t i
      have h := Nat.stirlingSecond_succ_succ (i + 1) t
      exact_mod_cast h
    have key : ∀ t : ℕ, ∑ i ∈ Finset.range (m + 1 + 1),
          ((m + 1).choose i : ℚ) * (-1 : ℚ) ^ i *
          (Nat.stirlingSecond (i + 1) (t + 1) : ℚ)
        = (∑ i ∈ Finset.range (m + 1), (m.choose i : ℚ) * (-1 : ℚ) ^ i *
            (Nat.stirlingSecond (i + 1) (t + 1) : ℚ))
          - (((t : ℚ) + 1) * (∑ i ∈ Finset.range (m + 1), (m.choose i : ℚ) *
            (-1 : ℚ) ^ i * (Nat.stirlingSecond (i + 1) (t + 1) : ℚ))
            + (∑ i ∈ Finset.range (m + 1), (m.choose i : ℚ) * (-1 : ℚ) ^ i *
              (Nat.stirlingSecond (i + 1) t : ℚ))) := by
      intro t
      have hQ : (∑ i ∈ Finset.range (m + 1), (m.choose (i + 1) : ℚ) *
            (-1 : ℚ) ^ (i + 1) * (Nat.stirlingSecond (i + 1 + 1) (t + 1) : ℚ))
          = (∑ i ∈ Finset.range (m + 1), (m.choose i : ℚ) * (-1 : ℚ) ^ i *
              (Nat.stirlingSecond (i + 1) (t + 1) : ℚ))
            - ((m.choose 0 : ℚ) * (-1 : ℚ) ^ 0 *
              (Nat.stirlingSecond (0 + 1) (t + 1) : ℚ)) := by
        have h1 : (∑ tt ∈ Finset.range (m + 1 + 1), (m.choose tt : ℚ) *
              (-1 : ℚ) ^ tt * (Nat.stirlingSecond (tt + 1) (t + 1) : ℚ))
            = (∑ i ∈ Finset.range (m + 1), (m.choose (i + 1) : ℚ) *
              (-1 : ℚ) ^ (i + 1) * (Nat.stirlingSecond (i + 1 + 1) (t + 1) : ℚ))
              + ((m.choose 0 : ℚ) * (-1 : ℚ) ^ 0 *
                (Nat.stirlingSecond (0 + 1) (t + 1) : ℚ)) :=
          Finset.sum_range_succ' _ _
        have h2 : (∑ tt ∈ Finset.range (m + 1 + 1), (m.choose tt : ℚ) *
              (-1 : ℚ) ^ tt * (Nat.stirlingSecond (tt + 1) (t + 1) : ℚ))
            = (∑ i ∈ Finset.range (m + 1), (m.choose i : ℚ) * (-1 : ℚ) ^ i *
              (Nat.stirlingSecond (i + 1) (t + 1) : ℚ)) := by
          rw [Finset.sum_range_succ]
          simp
        linarith [h1, h2]
      have hP : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℚ) *
            (-1 : ℚ) ^ (i + 1) * (Nat.stirlingSecond (i + 1 + 1) (t + 1) : ℚ))
          = -((((t : ℚ) + 1) * (∑ i ∈ Finset.range (m + 1), (m.choose i : ℚ) *
            (-1 : ℚ) ^ i * (Nat.stirlingSecond (i + 1) (t + 1) : ℚ)))
            + (∑ i ∈ Finset.range (m + 1), (m.choose i : ℚ) * (-1 : ℚ) ^ i *
              (Nat.stirlingSecond (i + 1) t : ℚ))) := by
        have hc : ∀ i ∈ Finset.range (m + 1), (m.choose i : ℚ) *
              (-1 : ℚ) ^ (i + 1) * (Nat.stirlingSecond (i + 1 + 1) (t + 1) : ℚ)
            = -((((t : ℚ) + 1) * ((m.choose i : ℚ) * (-1 : ℚ) ^ i *
              (Nat.stirlingSecond (i + 1) (t + 1) : ℚ)))
              + ((m.choose i : ℚ) * (-1 : ℚ) ^ i *
                (Nat.stirlingSecond (i + 1) t : ℚ))) := by
          intro i _
          rw [hS2 t i, pow_succ]
          ring
        rw [Finset.sum_congr rfl hc, Finset.sum_neg_distrib,
          Finset.sum_add_distrib, ← Finset.mul_sum]
      have hsplit : ∀ i ∈ Finset.range (m + 1), ((m + 1).choose (i + 1) : ℚ) *
            (-1 : ℚ) ^ (i + 1) * (Nat.stirlingSecond (i + 1 + 1) (t + 1) : ℚ)
          = ((m.choose i : ℚ) * (-1 : ℚ) ^ (i + 1) *
              (Nat.stirlingSecond (i + 1 + 1) (t + 1) : ℚ))
            + ((m.choose (i + 1) : ℚ) * (-1 : ℚ) ^ (i + 1) *
              (Nat.stirlingSecond (i + 1 + 1) (t + 1) : ℚ)) := by
        intro i _
        rw [pascal i]
        ring
      have hF0 : ((m + 1).choose 0 : ℚ) * (-1 : ℚ) ^ 0 *
            (Nat.stirlingSecond (0 + 1) (t + 1) : ℚ)
          = (m.choose 0 : ℚ) * (-1 : ℚ) ^ 0 *
            (Nat.stirlingSecond (0 + 1) (t + 1) : ℚ) := by
        simp [Nat.choose_zero_right]
      rw [Finset.sum_range_succ', Finset.sum_congr rfl hsplit,
        Finset.sum_add_distrib, hP, hQ, hF0]
      ring
    cases t with
    | zero =>
      have hB0 : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℚ) * (-1 : ℚ) ^ i *
          (Nat.stirlingSecond (i + 1) 0 : ℚ)) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        have h : (Nat.stirlingSecond (i + 1) 0 : ℚ) = 0 :=
          by exact_mod_cast Nat.stirlingSecond_succ_zero i
        rw [h, mul_zero]
      rw [key 0, ih 0, hB0, Nat.stirlingSecond_succ_zero]
      simp
    | succ j =>
      have hrec := Nat.stirlingSecond_succ_succ m j
      rw [key (j + 1), ih (j + 1), ih j, hrec]
      have hneg : (-1 : ℚ) ^ (m + 1) = -(-1 : ℚ) ^ m := by
        rw [pow_succ]
        ring
      rw [hneg]
      push_cast
      ring






private theorem aux_selfinv (k : ℕ) : (-1 : ℚ) ^ k * (-1 : ℚ) ^ k = 1 := by
  rw [← pow_add]
  have : k + k = 2 * k := by ring
  rw [this, pow_mul]
  norm_num

private theorem aux_sign (i j : ℕ) (hj : j ≤ i + 1) :
    (-1 : ℚ) ^ ((i + 1) - j) = (-1 : ℚ) ^ (i + 1) * (-1 : ℚ) ^ j := by
  have h1 : (-1 : ℚ) ^ (i + 1) = (-1 : ℚ) ^ ((i + 1) - j) * (-1 : ℚ) ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hj]
  have h2 : (-1 : ℚ) ^ j * (-1 : ℚ) ^ j = 1 := aux_selfinv j
  calc (-1 : ℚ) ^ ((i + 1) - j)
      = (-1 : ℚ) ^ ((i + 1) - j) * ((-1 : ℚ) ^ j * (-1 : ℚ) ^ j) := by
        rw [h2, mul_one]
    _ = ((-1 : ℚ) ^ ((i + 1) - j) * (-1 : ℚ) ^ j) * (-1 : ℚ) ^ j := by ring
    _ = (-1 : ℚ) ^ (i + 1) * (-1 : ℚ) ^ j := by rw [← h1]

private theorem aux_sign2 (n j : ℕ) (hj : j ≤ n) (hn : 1 ≤ n) :
    -(-1 : ℚ) ^ (n - 1 + j) = (-1 : ℚ) ^ (n - j) := by
  have e1 : n = (n - j) + j := (Nat.sub_add_cancel hj).symm
  have e2 : n = (n - 1) + 1 := by omega
  have h1 : (-1 : ℚ) ^ n = (-1 : ℚ) ^ (n - j) * (-1 : ℚ) ^ j := by
    conv_lhs => rw [e1]
    rw [pow_add]
  have h3 : (-1 : ℚ) ^ (n - 1) = -(-1 : ℚ) ^ n := by
    have h2 : (-1 : ℚ) ^ n = (-1 : ℚ) ^ (n - 1) * (-1 : ℚ) := by
      conv_lhs => rw [e2]
      rw [pow_add, pow_one]
    rw [h2]
    ring
  have h4 : (-1 : ℚ) ^ (n - 1 + j) = (-1 : ℚ) ^ (n - 1) * (-1 : ℚ) ^ j :=
    pow_add _ _ _
  have hs := aux_selfinv j
  rw [h4, h3, h1, ← neg_mul, neg_neg, mul_assoc, hs, mul_one]

private theorem aux_sign3 (n t : ℕ) (h : t < n) :
    (-1 : ℚ) ^ (n - t) + (-1 : ℚ) ^ ((n - 1) - t) = 0 := by
  have e : n - t = ((n - 1) - t) + 1 := by omega
  rw [e, pow_succ']
  ring

private theorem aux_kchoose (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    (k : ℚ) * (n.choose k : ℚ) = (n : ℚ) * ((n - 1).choose (k - 1) : ℚ) := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  have hN : (k' + 1) * (n' + 1).choose (k' + 1) = (n' + 1) * n'.choose k' := by
    have h1 := Nat.choose_succ_right_eq (n' + 1) k'
    have h2 := Nat.choose_mul_succ_eq n' k'
    calc (k' + 1) * (n' + 1).choose (k' + 1)
        = (n' + 1).choose k' * (n' + 1 - k') := by rw [mul_comm]; exact h1
      _ = (n' + 1) * n'.choose k' := by rw [← h2]; ring
  exact_mod_cast hN






private theorem aux_swap (n : ℕ) (f : ℕ → ℕ → ℚ) :
    ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.Icc 1 k, f k j
    = ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc j n, f k j := by
  trans ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.Icc 1 n, (if j ≤ k then f k j else 0)
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have hfil : Finset.filter (fun j => j ≤ k) (Finset.Icc 1 n) = Finset.Icc 1 k := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [← hfil, Finset.sum_filter]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    have hfil : Finset.filter (fun k => j ≤ k) (Finset.range (n + 1))
        = Finset.Icc j n := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      omega
    rw [← Finset.sum_filter, hfil]






private theorem aux_inner (n j : ℕ) (hn : 1 ≤ n) (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    ∑ k ∈ Finset.Icc j n, (n.choose k : ℚ) * (k : ℚ) * (-1 : ℚ) ^ (k - j) *
      (Nat.stirlingSecond k j : ℚ)
    = (n : ℚ) * (-1 : ℚ) ^ (n - j) * (Nat.stirlingSecond (n - 1) (j - 1) : ℚ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  have hinj : ∀ a ∈ Finset.Icc j (m + 1), ∀ b ∈ Finset.Icc j (m + 1),
      a - 1 = b - 1 → a = b := by
    intro a ha b hb hab
    rw [Finset.mem_Icc] at ha hb
    omega
  have eimg : Finset.image (fun k => k - 1) (Finset.Icc j (m + 1))
      = Finset.Icc (j - 1) m := by
    ext i
    simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · intro h
      obtain ⟨k, hk, hki⟩ := h
      omega
    · intro h
      obtain ⟨h1, h2⟩ := h
      refine ⟨i + 1, ?_, ?_⟩
      · omega
      · omega
  have s1 : (∑ k ∈ Finset.Icc j (m + 1), ((m + 1).choose k : ℚ) * (k : ℚ) *
        (-1 : ℚ) ^ (k - j) * (Nat.stirlingSecond k j : ℚ))
      = ((m + 1 : ℕ) : ℚ) * ∑ k ∈ Finset.Icc j (m + 1),
        (m.choose (k - 1) : ℚ) * (-1 : ℚ) ^ (k - j) *
        (Nat.stirlingSecond k j : ℚ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk1 : 1 ≤ k := by omega
    have hkk : k ≤ m + 1 := hk.2
    rw [mul_comm ((m + 1).choose k : ℚ) (k : ℚ), aux_kchoose (m + 1) k hk1 hkk]
    have eidx : m + 1 - 1 = m := by omega
    rw [eidx]
    ring
  have e1 : (∑ k ∈ Finset.Icc j (m + 1), (m.choose (k - 1) : ℚ) * (-1 : ℚ) ^ (k - j) *
        (Nat.stirlingSecond k j : ℚ))
      = ∑ i ∈ Finset.range (m + 1), (m.choose i : ℚ) * (-1 : ℚ) ^ ((i + 1) - j) *
        (Nat.stirlingSecond (i + 1) j : ℚ) := by
    have step1 : (∑ k ∈ Finset.Icc j (m + 1), (m.choose (k - 1) : ℚ) *
          (-1 : ℚ) ^ (k - j) * (Nat.stirlingSecond k j : ℚ))
        = ∑ i ∈ Finset.image (fun k => k - 1) (Finset.Icc j (m + 1)),
          (m.choose i : ℚ) * (-1 : ℚ) ^ ((i + 1) - j) *
          (Nat.stirlingSecond (i + 1) j : ℚ) := by
      rw [Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro k hk
      have hk1 : 1 ≤ k := by
        rw [Finset.mem_Icc] at hk
        omega
      have e : (k - 1) + 1 = k := by omega
      rw [e]
    rw [step1, eimg]
    apply Finset.sum_subset
    · intro i hi
      rw [Finset.mem_Icc] at hi
      rw [Finset.mem_range]
      omega
    · intro i hi hlo
      rw [Finset.mem_range] at hi
      rw [Finset.mem_Icc] at hlo
      by_cases hle : j - 1 ≤ i
      · have hC : m.choose i = 0 := by
          apply Nat.choose_eq_zero_of_lt
          by_contra hcon
          have hle2 : i ≤ m := by omega
          exact hlo ⟨hle, hle2⟩
        simp [hC]
      · have hS : Nat.stirlingSecond (i + 1) j = 0 :=
          Nat.stirlingSecond_eq_zero_of_lt (by omega)
        simp [hS]
  have e4 : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℚ) * (-1 : ℚ) ^ ((i + 1) - j) *
        (Nat.stirlingSecond (i + 1) j : ℚ))
      = (-1 : ℚ) ^ j * (-((-1 : ℚ) ^ m * (Nat.stirlingSecond m (j - 1) : ℚ))) := by
    have econv : ∀ i ∈ Finset.range (m + 1), (m.choose i : ℚ) * (-1 : ℚ) ^ ((i + 1) - j) *
          (Nat.stirlingSecond (i + 1) j : ℚ)
        = (-1 : ℚ) ^ j * ((m.choose i : ℚ) * (-((-1 : ℚ) ^ i)) *
          (Nat.stirlingSecond (i + 1) j : ℚ)) := by
      intro i _
      by_cases h : j ≤ i + 1
      · rw [aux_sign i j h, pow_succ]
        ring
      · have hS : Nat.stirlingSecond (i + 1) j = 0 :=
          Nat.stirlingSecond_eq_zero_of_lt (by omega)
        simp [hS]
    have eneg : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℚ) * (-((-1 : ℚ) ^ i)) *
          (Nat.stirlingSecond (i + 1) j : ℚ))
        = -(∑ i ∈ Finset.range (m + 1), (m.choose i : ℚ) * (-1 : ℚ) ^ i *
          (Nat.stirlingSecond (i + 1) j : ℚ)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have ej : j - 1 + 1 = j := by omega
    have hH := aux_stirling m (j - 1)
    rw [ej] at hH
    rw [Finset.sum_congr rfl econv, ← Finset.mul_sum, eneg, hH]
  have hsign : -(-1 : ℚ) ^ (j + m) = (-1 : ℚ) ^ ((m + 1) - j) := by
    have h := aux_sign2 (m + 1) j hjn (by omega)
    have e : (m + 1) - 1 + j = j + m := by omega
    rw [e] at h
    exact h
  have efinal : (-1 : ℚ) ^ j * (-((-1 : ℚ) ^ m * (Nat.stirlingSecond m (j - 1) : ℚ)))
      = (-1 : ℚ) ^ ((m + 1) - j) * (Nat.stirlingSecond m (j - 1) : ℚ) := by
    have h1 : (-1 : ℚ) ^ j * (-1 : ℚ) ^ m = (-1 : ℚ) ^ (j + m) :=
      (pow_add (-1 : ℚ) j m).symm
    have h2 : (-1 : ℚ) ^ j * (-((-1 : ℚ) ^ m * (Nat.stirlingSecond m (j - 1) : ℚ)))
        = -(((-1 : ℚ) ^ j * (-1 : ℚ) ^ m) * (Nat.stirlingSecond m (j - 1) : ℚ)) := by
      ring
    rw [h2, h1, ← neg_mul, hsign]
  rw [s1, e1, e4, efinal, mul_assoc]

private theorem aux_cfact (j : ℕ) (hj : 1 ≤ j) :
    (Nat.factorial (j - 1) : ℚ) / (2 : ℚ) ^ (j - 1) * (j : ℚ)
      = 2 * ((Nat.factorial j : ℚ) / (2 : ℚ) ^ j) := by
  obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  rw [Nat.factorial_succ, pow_succ']
  have h2 : (2 : ℚ) ^ j' ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2' : (2 : ℚ) * (2 : ℚ) ^ j' ≠ 0 := mul_ne_zero two_ne_zero h2
  field_simp
  push_cast
  ring

private theorem aux_Icc_range (Ga : ℕ → ℚ) (n : ℕ) (h0 : Ga 0 = 0) (hn : Ga n = 0) :
    ∑ j ∈ Finset.Icc 1 n, Ga j = ∑ t ∈ Finset.range n, Ga t := by
  have f1 : Finset.filter (fun k => 1 ≤ k ∧ k ≤ n) (Finset.range (n + 1))
      = Finset.Icc 1 n := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  have f2 : Finset.filter (fun k => k < n) (Finset.range (n + 1))
      = Finset.range n := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← f1, ← f2, Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk0 : k = 0
  · subst hk0
    by_cases hn0 : 0 < n
    · simp [hn0, h0]
    · simp [hn0]
  · by_cases hkn : k = n
    · subst k
      have c1 : 1 ≤ n := by omega
      simp [c1, hn]
    · have hc : (1 ≤ k ∧ k ≤ n) ↔ k < n := by omega
      simp only [hc]

private theorem aux_Fconv (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) *
      ((k : ℚ) * ∑ j ∈ Finset.Icc 1 k,
        (((-1 : ℚ) ^ (k - j) * (Nat.factorial (j - 1) : ℚ) *
          (Nat.stirlingSecond k j : ℚ)) / (2 : ℚ) ^ (j - 1)))
      = -((n : ℚ) * ∑ j ∈ Finset.Icc 1 n,
        (((-1 : ℚ) ^ (n - j) * (Nat.factorial (j - 1) : ℚ) *
          (Nat.stirlingSecond n j : ℚ)) / (2 : ℚ) ^ (j - 1)))
        + (if n = 1 then (2 : ℚ) else 0) := by
  by_cases h0 : n = 0
  · subst h0
    simp
  by_cases h1 : n = 1
  · subst h1
    simp [Finset.sum_range_succ, Finset.Icc_self,
      Finset.sum_singleton, Nat.stirlingSecond_self]
    norm_num
  · have hn2 : 2 ≤ n := by omega
    have hn1 : 1 ≤ n := by omega
    simp only [h1, ite_false]
    rw [add_zero, eq_neg_iff_add_eq_zero]
    have step1 : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) *
          ((k : ℚ) * ∑ j ∈ Finset.Icc 1 k,
            (((-1 : ℚ) ^ (k - j) * (Nat.factorial (j - 1) : ℚ) *
              (Nat.stirlingSecond k j : ℚ)) / (2 : ℚ) ^ (j - 1))))
        = ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.Icc 1 k,
          (((n.choose k : ℚ) * (k : ℚ)) * (((-1 : ℚ) ^ (k - j) *
            (Nat.factorial (j - 1) : ℚ) * (Nat.stirlingSecond k j : ℚ)) /
            (2 : ℚ) ^ (j - 1))) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← mul_assoc, Finset.mul_sum]
    have swap : (∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.Icc 1 k,
          (((n.choose k : ℚ) * (k : ℚ)) * (((-1 : ℚ) ^ (k - j) *
            (Nat.factorial (j - 1) : ℚ) * (Nat.stirlingSecond k j : ℚ)) /
            (2 : ℚ) ^ (j - 1))))
        = ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc j n,
          (((n.choose k : ℚ) * (k : ℚ)) * (((-1 : ℚ) ^ (k - j) *
            (Nat.factorial (j - 1) : ℚ) * (Nat.stirlingSecond k j : ℚ)) /
            (2 : ℚ) ^ (j - 1))) :=
      aux_swap n (fun k j => (((n.choose k : ℚ) * (k : ℚ)) *
        (((-1 : ℚ) ^ (k - j) * (Nat.factorial (j - 1) : ℚ) *
          (Nat.stirlingSecond k j : ℚ)) / (2 : ℚ) ^ (j - 1))))
    have hinner : ∀ j ∈ Finset.Icc 1 n,
        (∑ k ∈ Finset.Icc j n, (((n.choose k : ℚ) * (k : ℚ)) *
          (((-1 : ℚ) ^ (k - j) * (Nat.factorial (j - 1) : ℚ) *
            (Nat.stirlingSecond k j : ℚ)) / (2 : ℚ) ^ (j - 1))))
        = ((Nat.factorial (j - 1) : ℚ) / (2 : ℚ) ^ (j - 1)) *
          ((n : ℚ) * (-1 : ℚ) ^ (n - j) *
            (Nat.stirlingSecond (n - 1) (j - 1) : ℚ)) := by
      intro j hj
      have hmem1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hmem2 : j ≤ n := (Finset.mem_Icc.mp hj).2
      have efac : ∀ k ∈ Finset.Icc j n,
          (((n.choose k : ℚ) * (k : ℚ)) * (((-1 : ℚ) ^ (k - j) *
            (Nat.factorial (j - 1) : ℚ) * (Nat.stirlingSecond k j : ℚ)) /
            (2 : ℚ) ^ (j - 1)))
          = ((Nat.factorial (j - 1) : ℚ) / (2 : ℚ) ^ (j - 1)) *
            (((n.choose k : ℚ) * (k : ℚ) * (-1 : ℚ) ^ (k - j) *
              (Nat.stirlingSecond k j : ℚ))) := by
        intro k _
        ring
      rw [Finset.sum_congr rfl efac, ← Finset.mul_sum,
        aux_inner n j hn1 hmem1 hmem2]
    have hLHS : (∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc j n,
          (((n.choose k : ℚ) * (k : ℚ)) * (((-1 : ℚ) ^ (k - j) *
            (Nat.factorial (j - 1) : ℚ) * (Nat.stirlingSecond k j : ℚ)) /
            (2 : ℚ) ^ (j - 1))))
        = (n : ℚ) * ∑ j ∈ Finset.Icc 1 n,
          (((Nat.factorial (j - 1) : ℚ) / (2 : ℚ) ^ (j - 1)) *
            (((-1 : ℚ) ^ (n - j)) *
              (Nat.stirlingSecond (n - 1) (j - 1) : ℚ))) := by
      have e1 : ∀ j ∈ Finset.Icc 1 n, (∑ k ∈ Finset.Icc j n,
            (((n.choose k : ℚ) * (k : ℚ)) * (((-1 : ℚ) ^ (k - j) *
              (Nat.factorial (j - 1) : ℚ) * (Nat.stirlingSecond k j : ℚ)) /
              (2 : ℚ) ^ (j - 1))))
          = (n : ℚ) * (((Nat.factorial (j - 1) : ℚ) / (2 : ℚ) ^ (j - 1)) *
            (((-1 : ℚ) ^ (n - j)) *
              (Nat.stirlingSecond (n - 1) (j - 1) : ℚ))) := by
        intro j hj
        rw [hinner j hj]
        ring
      rw [Finset.sum_congr rfl e1, ← Finset.mul_sum]
    rw [step1, swap, hLHS]
    have hcomb : (n : ℚ) * (∑ j ∈ Finset.Icc 1 n,
          (((Nat.factorial (j - 1) : ℚ) / (2 : ℚ) ^ (j - 1)) *
            (((-1 : ℚ) ^ (n - j)) *
              (Nat.stirlingSecond (n - 1) (j - 1) : ℚ))))
        + (n : ℚ) * (∑ j ∈ Finset.Icc 1 n,
          (((-1 : ℚ) ^ (n - j) * (Nat.factorial (j - 1) : ℚ) *
            (Nat.stirlingSecond n j : ℚ)) / (2 : ℚ) ^ (j - 1)))
        = (n : ℚ) * (∑ j ∈ Finset.Icc 1 n,
          ((((Nat.factorial (j - 1) : ℚ) / (2 : ℚ) ^ (j - 1)) *
            (((-1 : ℚ) ^ (n - j)) *
              (Nat.stirlingSecond (n - 1) (j - 1) : ℚ)))
          + (((-1 : ℚ) ^ (n - j) * (Nat.factorial (j - 1) : ℚ) *
            (Nat.stirlingSecond n j : ℚ)) / (2 : ℚ) ^ (j - 1)))) := by
      rw [← mul_add, ← Finset.sum_add_distrib]
    rw [hcomb]
    have hpq : ∀ j ∈ Finset.Icc 1 n,
        ((((Nat.factorial (j - 1) : ℚ) / (2 : ℚ) ^ (j - 1)) *
          (((-1 : ℚ) ^ (n - j)) *
            (Nat.stirlingSecond (n - 1) (j - 1) : ℚ)))
        + (((-1 : ℚ) ^ (n - j) * (Nat.factorial (j - 1) : ℚ) *
          (Nat.stirlingSecond n j : ℚ)) / (2 : ℚ) ^ (j - 1)))
        = (2 * ((((Nat.factorial (j - 1) : ℚ) / (2 : ℚ) ^ (j - 1)) *
          (((-1 : ℚ) ^ (n - j)) *
            (Nat.stirlingSecond (n - 1) (j - 1) : ℚ)))))
          + 2 * ((((Nat.factorial j : ℚ) / (2 : ℚ) ^ j) *
          (((-1 : ℚ) ^ (n - j)) *
            (Nat.stirlingSecond (n - 1) j : ℚ)))) := by
      intro j hj
      have hmem1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hS : (Nat.stirlingSecond n j : ℚ) = (j : ℚ) *
          (Nat.stirlingSecond (n - 1) j : ℚ) +
          (Nat.stirlingSecond (n - 1) (j - 1) : ℚ) := by
        have h := Nat.stirlingSecond_succ_succ (n - 1) (j - 1)
        have en : n - 1 + 1 = n := by omega
        have ej : j - 1 + 1 = j := by omega
        rw [en, ej] at h
        exact_mod_cast h
      have hA : (((-1 : ℚ) ^ (n - j) * (Nat.factorial (j - 1) : ℚ) *
          (Nat.stirlingSecond n j : ℚ)) / (2 : ℚ) ^ (j - 1))
          = ((Nat.factorial (j - 1) : ℚ) / (2 : ℚ) ^ (j - 1)) *
            (((-1 : ℚ) ^ (n - j)) * (Nat.stirlingSecond n j : ℚ)) := by
        ring
      have hcd := aux_cfact j hmem1
      have e1 : ((Nat.factorial (j - 1) : ℚ) / (2 : ℚ) ^ (j - 1)) *
            (((-1 : ℚ) ^ (n - j)) * ((j : ℚ) *
              (Nat.stirlingSecond (n - 1) j : ℚ) +
              (Nat.stirlingSecond (n - 1) (j - 1) : ℚ)))
          = (((Nat.factorial (j - 1) : ℚ) / (2 : ℚ) ^ (j - 1)) * (j : ℚ)) *
            (((-1 : ℚ) ^ (n - j)) * (Nat.stirlingSecond (n - 1) j : ℚ)) +
            ((Nat.factorial (j - 1) : ℚ) / (2 : ℚ) ^ (j - 1)) *
            (((-1 : ℚ) ^ (n - j)) *
              (Nat.stirlingSecond (n - 1) (j - 1) : ℚ)) := by
        ring
      rw [hA, hS, e1, hcd]
      ring
    have hSb : (∑ j ∈ Finset.Icc 1 n,
          (((Nat.factorial (j - 1) : ℚ) / (2 : ℚ) ^ (j - 1)) *
            (((-1 : ℚ) ^ (n - j)) *
              (Nat.stirlingSecond (n - 1) (j - 1) : ℚ))))
        = ∑ t ∈ Finset.range n,
          (((Nat.factorial t : ℚ) / (2 : ℚ) ^ t) *
            (((-1 : ℚ) ^ ((n - 1) - t)) *
              (Nat.stirlingSecond (n - 1) t : ℚ))) := by
      have hIccIco : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      rw [hIccIco, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
      apply Finset.sum_congr rfl
      intro i hi
      have hii : i < n := Finset.mem_range.mp hi
      have ein : (1 + i) - 1 = i := by omega
      have eexp : n - (1 + i) = (n - 1) - i := by omega
      change (((Nat.factorial ((1 + i) - 1) : ℚ) / (2 : ℚ) ^ ((1 + i) - 1)) *
          (((-1 : ℚ) ^ (n - (1 + i))) *
            (Nat.stirlingSecond (n - 1) ((1 + i) - 1) : ℚ)))
        = (((Nat.factorial i : ℚ) / (2 : ℚ) ^ i) *
          (((-1 : ℚ) ^ ((n - 1) - i)) * (Nat.stirlingSecond (n - 1) i : ℚ)))
      rw [ein, eexp]
    have hSa0 : (fun j => ((Nat.factorial j : ℚ) / (2 : ℚ) ^ j) *
          (((-1 : ℚ) ^ (n - j)) * (Nat.stirlingSecond (n - 1) j : ℚ))) 0 = 0 := by
      change ((Nat.factorial 0 : ℚ) / (2 : ℚ) ^ 0) *
          (((-1 : ℚ) ^ (n - 0)) * (Nat.stirlingSecond (n - 1) 0 : ℚ)) = 0
      have hS0 : Nat.stirlingSecond (n - 1) 0 = 0 := by
        have e : n - 1 = Nat.succ (n - 2) := by omega
        rw [e]
        exact Nat.stirlingSecond_succ_zero _
      simp [hS0]
    have hSan : (fun j => ((Nat.factorial j : ℚ) / (2 : ℚ) ^ j) *
          (((-1 : ℚ) ^ (n - j)) * (Nat.stirlingSecond (n - 1) j : ℚ))) n = 0 := by
      change ((Nat.factorial n : ℚ) / (2 : ℚ) ^ n) *
          (((-1 : ℚ) ^ (n - n)) * (Nat.stirlingSecond (n - 1) n : ℚ)) = 0
      have hSn : Nat.stirlingSecond (n - 1) n = 0 :=
        Nat.stirlingSecond_eq_zero_of_lt (by omega)
      simp [hSn]
    have hSa : (∑ j ∈ Finset.Icc 1 n,
          (((Nat.factorial j : ℚ) / (2 : ℚ) ^ j) *
            (((-1 : ℚ) ^ (n - j)) * (Nat.stirlingSecond (n - 1) j : ℚ))))
        = ∑ t ∈ Finset.range n,
          (((Nat.factorial t : ℚ) / (2 : ℚ) ^ t) *
            (((-1 : ℚ) ^ (n - t)) * (Nat.stirlingSecond (n - 1) t : ℚ))) :=
      aux_Icc_range _ n hSa0 hSan
    have h0 : (∑ t ∈ Finset.range n,
          (((Nat.factorial t : ℚ) / (2 : ℚ) ^ t) *
            (((-1 : ℚ) ^ ((n - 1) - t)) * (Nat.stirlingSecond (n - 1) t : ℚ))))
        + (∑ t ∈ Finset.range n,
          (((Nat.factorial t : ℚ) / (2 : ℚ) ^ t) *
            (((-1 : ℚ) ^ (n - t)) * (Nat.stirlingSecond (n - 1) t : ℚ)))) = 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro t ht
      have htt : t < n := Finset.mem_range.mp ht
      have hs3 : (-1 : ℚ) ^ ((n - 1) - t) + (-1 : ℚ) ^ (n - t) = 0 := by
        rw [add_comm]
        exact aux_sign3 n t htt
      have e : (((Nat.factorial t : ℚ) / (2 : ℚ) ^ t) *
            (((-1 : ℚ) ^ ((n - 1) - t)) * (Nat.stirlingSecond (n - 1) t : ℚ)))
          + (((Nat.factorial t : ℚ) / (2 : ℚ) ^ t) *
            (((-1 : ℚ) ^ (n - t)) * (Nat.stirlingSecond (n - 1) t : ℚ)))
          = ((Nat.factorial t : ℚ) / (2 : ℚ) ^ t) *
            (((-1 : ℚ) ^ ((n - 1) - t) + (-1 : ℚ) ^ (n - t))) *
            (Nat.stirlingSecond (n - 1) t : ℚ) := by
        ring
      rw [e, hs3, mul_zero, zero_mul]
    have hzero : (∑ j ∈ Finset.Icc 1 n,
          ((((Nat.factorial (j - 1) : ℚ) / (2 : ℚ) ^ (j - 1)) *
            (((-1 : ℚ) ^ (n - j)) *
              (Nat.stirlingSecond (n - 1) (j - 1) : ℚ)))
          + (((-1 : ℚ) ^ (n - j) * (Nat.factorial (j - 1) : ℚ) *
            (Nat.stirlingSecond n j : ℚ)) / (2 : ℚ) ^ (j - 1)))) = 0 := by
      have ePQ : ∀ j ∈ Finset.Icc 1 n,
          ((((Nat.factorial (j - 1) : ℚ) / (2 : ℚ) ^ (j - 1)) *
            (((-1 : ℚ) ^ (n - j)) *
              (Nat.stirlingSecond (n - 1) (j - 1) : ℚ)))
          + (((-1 : ℚ) ^ (n - j) * (Nat.factorial (j - 1) : ℚ) *
            (Nat.stirlingSecond n j : ℚ)) / (2 : ℚ) ^ (j - 1)))
          = (2 * ((((Nat.factorial (j - 1) : ℚ) / (2 : ℚ) ^ (j - 1)) *
            (((-1 : ℚ) ^ (n - j)) *
              (Nat.stirlingSecond (n - 1) (j - 1) : ℚ)))))
            + 2 * ((((Nat.factorial j : ℚ) / (2 : ℚ) ^ j) *
            (((-1 : ℚ) ^ (n - j)) *
              (Nat.stirlingSecond (n - 1) j : ℚ)))) := by
        intro j hj
        exact hpq j hj
      rw [Finset.sum_congr rfl ePQ, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, hSb, hSa]
      linarith
    rw [hzero, mul_zero]

private def aux_H (n : ℕ) : ℚ :=
  (n : ℚ) * ∑ j ∈ Finset.Icc 1 n,
    (((-1 : ℚ) ^ (n - j) * (Nat.factorial (j - 1) : ℚ) *
      (Nat.stirlingSecond n j : ℚ)) / (2 : ℚ) ^ (j - 1))

private def aux_G (n : ℕ) : ℚ :=
  2 * (1 - (2 : ℚ) ^ n) * bernoulli n

private theorem aux_Hrel (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * aux_H k) + aux_H n
    = (if n = 1 then (2 : ℚ) else 0) := by
  unfold aux_H
  have h := aux_Fconv n
  linarith

private theorem aux_rescale_X :
    (PowerSeries.rescale 2) (PowerSeries.X : PowerSeries ℚ) = 2 • PowerSeries.X := by
  ext n
  by_cases hn : n = 1
  · subst hn
    simp [PowerSeries.coeff_X]
  · simp [PowerSeries.coeff_X, hn]

private theorem aux_exp_sq : (PowerSeries.exp ℚ) ^ 2
    = (PowerSeries.rescale 2) (PowerSeries.exp ℚ) := by
  have h := PowerSeries.exp_pow_eq_rescale_exp (A := ℚ) 2
  simpa using h

private theorem aux_B2ser :
    (PowerSeries.rescale 2) (bernoulliPowerSeries ℚ) * ((PowerSeries.exp ℚ) ^ 2 - 1)
      = 2 • PowerSeries.X := by
  have hB : bernoulliPowerSeries ℚ * (PowerSeries.exp ℚ - 1) = PowerSeries.X :=
    bernoulliPowerSeries_mul_exp_sub_one ℚ
  have h := congrArg (fun x : PowerSeries ℚ => (PowerSeries.rescale 2) x) hB
  simp only [map_mul, map_sub, map_one] at h
  rw [← aux_exp_sq, aux_rescale_X] at h
  exact h

private theorem aux_exp_ne : PowerSeries.exp ℚ - 1 ≠ 0 := by
  intro h0
  have hc : (PowerSeries.coeff 1) (PowerSeries.exp ℚ - 1) = 0 := by
    rw [h0]
    simp
  simp [map_sub, PowerSeries.coeff_exp] at hc

private theorem aux_key :
    (PowerSeries.rescale 2) (bernoulliPowerSeries ℚ) * (PowerSeries.exp ℚ + 1)
      = 2 • (bernoulliPowerSeries ℚ) := by
  have hB : bernoulliPowerSeries ℚ * (PowerSeries.exp ℚ - 1) = PowerSeries.X :=
    bernoulliPowerSeries_mul_exp_sub_one ℚ
  apply mul_left_cancel₀ aux_exp_ne
  calc (PowerSeries.exp ℚ - 1) *
        ((PowerSeries.rescale 2) (bernoulliPowerSeries ℚ) * (PowerSeries.exp ℚ + 1))
      = (PowerSeries.rescale 2) (bernoulliPowerSeries ℚ) * ((PowerSeries.exp ℚ) ^ 2 - 1) := by ring
    _ = 2 • PowerSeries.X := aux_B2ser
    _ = (PowerSeries.exp ℚ - 1) * (2 • bernoulliPowerSeries ℚ) := by
        rw [← hB]
        ring

private theorem aux_coeffB (k : ℕ) :
    (PowerSeries.coeff k) ((PowerSeries.rescale 2) (bernoulliPowerSeries ℚ))
      = (2 : ℚ) ^ k * (bernoulli k / (Nat.factorial k : ℚ)) := by
  rw [PowerSeries.coeff_rescale]
  congr 1
  unfold bernoulliPowerSeries
  rw [PowerSeries.coeff_mk]
  simp

private theorem aux_coeffExp (j : ℕ) :
    (PowerSeries.coeff j) (PowerSeries.exp ℚ) = 1 / (Nat.factorial j : ℚ) := by
  rw [PowerSeries.coeff_exp]
  simp

private theorem aux_perterm (N k : ℕ) (hkn : k ≤ N) :
    (Nat.factorial N : ℚ) *
      (((2 : ℚ) ^ k * (bernoulli k / (Nat.factorial k : ℚ))) * (1 / (Nat.factorial (N - k) : ℚ)))
    = (N.choose k : ℚ) * (2 : ℚ) ^ k * bernoulli k := by
  have h := Nat.choose_mul_factorial_mul_factorial hkn
  have hfact : (N.choose k : ℚ) * (Nat.factorial k : ℚ) * (Nat.factorial (N - k) : ℚ)
      = (Nat.factorial N : ℚ) := by exact_mod_cast h
  have hk0 : (Nat.factorial k : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hNk0 : (Nat.factorial (N - k) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (N - k)
  have hC : (Nat.factorial N : ℚ) / ((Nat.factorial k : ℚ) * (Nat.factorial (N - k) : ℚ))
      = (N.choose k : ℚ) := by
    rw [div_eq_iff (mul_ne_zero hk0 hNk0), ← mul_assoc]
    exact hfact.symm
  have ering : (Nat.factorial N : ℚ) *
      ((2 : ℚ) ^ k * (bernoulli k / (Nat.factorial k : ℚ)) * (1 / (Nat.factorial (N - k) : ℚ)))
      = ((Nat.factorial N : ℚ) / ((Nat.factorial k : ℚ) * (Nat.factorial (N - k) : ℚ))) *
        ((2 : ℚ) ^ k * bernoulli k) := by
    ring
  rw [ering, hC]
  ring

private theorem aux_diag (N : ℕ) : (Nat.factorial N : ℚ) *
    (PowerSeries.coeff N) ((PowerSeries.rescale 2) (bernoulliPowerSeries ℚ))
    = (2 : ℚ) ^ N * bernoulli N := by
  rw [aux_coeffB]
  field_simp

private theorem aux_rhs (N : ℕ) : (Nat.factorial N : ℚ) *
    (PowerSeries.coeff N) (2 • bernoulliPowerSeries ℚ) = 2 * bernoulli N := by
  have e : (PowerSeries.coeff N) (2 • bernoulliPowerSeries ℚ)
      = 2 * (bernoulli N / (Nat.factorial N : ℚ)) := by
    simp [bernoulliPowerSeries, PowerSeries.coeff_mk]
  rw [e]
  field_simp

private theorem aux_main (N : ℕ) : (Nat.factorial N : ℚ) *
    (PowerSeries.coeff N) ((PowerSeries.rescale 2) (bernoulliPowerSeries ℚ) * PowerSeries.exp ℚ)
    = ∑ k ∈ Finset.range (N + 1), (N.choose k : ℚ) * (2 : ℚ) ^ k * bernoulli k := by
  have step1 : (PowerSeries.coeff N)
      ((PowerSeries.rescale 2) (bernoulliPowerSeries ℚ) * PowerSeries.exp ℚ)
      = ∑ k ∈ Finset.range (N + 1),
        (PowerSeries.coeff k) ((PowerSeries.rescale 2) (bernoulliPowerSeries ℚ)) *
        (PowerSeries.coeff (N - k)) (PowerSeries.exp ℚ) := by
    rw [PowerSeries.coeff_mul]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (PowerSeries.coeff i) ((PowerSeries.rescale 2) (bernoulliPowerSeries ℚ)) *
        (PowerSeries.coeff j) (PowerSeries.exp ℚ)) N]
  rw [step1, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_range] at hk
  have hkn : k ≤ N := by omega
  change (Nat.factorial N : ℚ) * ((PowerSeries.coeff k) _ * (PowerSeries.coeff (N - k)) _) = _
  rw [aux_coeffB, aux_coeffExp]
  exact aux_perterm N k hkn

private theorem aux_bernoulli_half (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), (N.choose k : ℚ) * (2 : ℚ) ^ k * bernoulli k
    = (2 - (2 : ℚ) ^ N) * bernoulli N := by
  have hcoeff := congrArg
    (fun x : PowerSeries ℚ => (Nat.factorial N : ℚ) * (PowerSeries.coeff N) x) aux_key
  have split : (PowerSeries.coeff N)
      ((PowerSeries.rescale 2) (bernoulliPowerSeries ℚ) * (PowerSeries.exp ℚ + 1))
      = (PowerSeries.coeff N) ((PowerSeries.rescale 2) (bernoulliPowerSeries ℚ) * PowerSeries.exp ℚ)
        + (PowerSeries.coeff N) ((PowerSeries.rescale 2) (bernoulliPowerSeries ℚ)) := by
    rw [mul_add, map_add, mul_one]
  rw [split, mul_add, aux_main, aux_diag, aux_rhs] at hcoeff
  linarith

private theorem aux_Grel (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * aux_G k) + aux_G n
    = (if n = 1 then (2 : ℚ) else 0) := by
  unfold aux_G
  have hT := aux_bernoulli_half n
  have hS := sum_bernoulli n
  have e1 : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * (2 * (1 - (2 : ℚ) ^ k) * bernoulli k))
      = 2 * (∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * bernoulli k)
        - 2 * (∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * (2 : ℚ) ^ k * bernoulli k) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => by ring)
  have e2 : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * bernoulli k)
      = (if n = 1 then (1 : ℚ) else 0) + bernoulli n := by
    rw [Finset.sum_range_succ, hS, Nat.choose_self, Nat.cast_one, one_mul]
  rw [e1, e2, hT]
  by_cases hn : n = 1
  · subst hn
    simp only [ite_true]
    ring
  · simp only [hn, ite_false]
    ring

private theorem aux_unique : ∀ n, aux_H n = aux_G n := by
  intro n
  refine Nat.strong_induction_on n (fun n ih => ?_)
  have hHn := aux_Hrel n
  have hGn := aux_Grel n
  have eH : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * aux_H k)
      = (∑ k ∈ Finset.range n, (n.choose k : ℚ) * aux_H k) + aux_H n := by
    rw [Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul]
  have eG : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * aux_G k)
      = (∑ k ∈ Finset.range n, (n.choose k : ℚ) * aux_G k) + aux_G n := by
    rw [Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul]
  have hsum : (∑ k ∈ Finset.range n, (n.choose k : ℚ) * aux_H k)
      = ∑ k ∈ Finset.range n, (n.choose k : ℚ) * aux_G k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [ih k hk]
  rw [eH, hsum] at hHn
  rw [eG] at hGn
  linarith

/-- **Garabedian's formula for the Bernoulli numbers, including $n = 0$.** For every natural
number $n$,

$$2(1 - 2^n) B_n = n \sum_{k=1}^{n} \frac{(-1)^{n-k} (k-1)!\, S(n, k)}{2^{k-1}},$$

where $B_n$ is the $n$-th Bernoulli number, with $B_1 = -\frac{1}{2}$, and $S(n, k)$ is the
Stirling number of the second kind. At $n = 0$ both sides are $0$. -/
theorem garabedian_genocchi_formula_general (n : ℕ) :
    2 * (1 - (2 : ℚ) ^ n) * bernoulli n =
      n * ∑ k ∈ Finset.Icc 1 n,
        ((-1 : ℚ) ^ (n - k) * (Nat.factorial (k - 1) : ℚ) *
          Nat.stirlingSecond n k) / (2 : ℚ) ^ (k - 1) := by
  have h := aux_unique n
  unfold aux_H aux_G at h
  exact h.symm

set_option linter.unusedVariables false in
/-- **Garabedian's formula for the Bernoulli numbers.** For every natural number $n \ge 1$,

$$2(1 - 2^n) B_n = n \sum_{k=1}^{n} \frac{(-1)^{n-k} (k-1)!\, S(n, k)}{2^{k-1}},$$

where $B_n$ is the $n$-th Bernoulli number, with $B_1 = -\frac{1}{2}$, and $S(n, k)$ is the
Stirling number of the second kind.

The identity also holds for $n = 0$, where both sides are $0$.

Proves `Wanted` entry `garabedian_genocchi_formula`.

Source: Schehrazade Zerroukhat and Laala Khaldi, "A Note on Explicit Formulas
for Bernoulli and Genocchi Numbers," Journal of Integer Sequences 28 (2025),
Article 25.6.7, equation (g19), lines 188–191 of the official TeX,
<https://cs.uwaterloo.ca/journals/JIS/VOL28/Zerroukhat/zerrou3.tex>,
which displays `2(1-2^n)B_n = G_n = n ∑ ...` and notes Garabedian's formula
is equivalent to it; this module formalizes the outer (Bernoulli-to-sum)
equality. Original: H. L. Garabedian, "A new formula for the Bernoulli
numbers," Bull. Amer. Math. Soc. 46 (1940), 531–533.
-/
@[nolint unusedArguments]
theorem garabedian_genocchi_formula (n : ℕ) (hn : 1 ≤ n) :
    2 * (1 - (2 : ℚ) ^ n) * bernoulli n =
      n * ∑ k ∈ Finset.Icc 1 n,
        ((-1 : ℚ) ^ (n - k) * (Nat.factorial (k - 1) : ℚ) *
          Nat.stirlingSecond n k) / (2 : ℚ) ^ (k - 1) := by
  exact garabedian_genocchi_formula_general n

end

end MetaMathlibExt
