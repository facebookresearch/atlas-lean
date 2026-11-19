/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace Cslib.Algorithms.Lean.Geometry.BSpline

/-- B-spline basis by Cox-de Boor. Real division by zero is zero in Lean,
which is exactly the 0/0 := 0 convention for repeated knots. -/
noncomputable def B (t : ℕ → ℝ) (i : ℕ) : ℕ → ℝ → ℝ
  | 0, x => if t i ≤ x ∧ x < t (i + 1) then 1 else 0
  | k + 1, x =>
    (x - t i) / (t (i + k + 1) - t i) * B t i k x +
      (t (i + k + 2) - x) / (t (i + k + 2) - t (i + 1)) * B t (i + 1) k x

/-- L1. Local support: nonzero only on `[t i, t (i + k + 1))`. -/
theorem B_local_support {t : ℕ → ℝ} {i k : ℕ} {x : ℝ}
    (ht : Monotone t) (h : B t i k x ≠ 0) :
    t i ≤ x ∧ x < t (i + k + 1) := by
  revert h
  revert i
  induction k with
  | zero =>
    intro i h
    simp only [B] at h
    have hc : t i ≤ x ∧ x < t (i + 1) := by
      by_contra hc
      exact h (ite_eq_right hc)
    simpa using hc
  | succ k ih =>
    intro i h
    simp only [B] at h
    have hB : B t i k x ≠ 0 ∨ B t (i + 1) k x ≠ 0 := by
      by_contra hc
      have hz1 : B t i k x = 0 := by
        by_contra hz1
        exact hc (Or.inl hz1)
      have hz2 : B t (i + 1) k x = 0 := by
        by_contra hz2
        exact hc (Or.inr hz2)
      simp only [hz1, hz2, mul_zero, add_zero] at h
      exact h rfl
    cases hB with
    | inl hB =>
      obtain ⟨hlo, hhi⟩ := @ih i hB
      exact ⟨hlo, lt_of_lt_of_le hhi (ht (by omega))⟩
    | inr hB =>
      obtain ⟨hlo, hhi⟩ := @ih (i + 1) hB
      refine ⟨le_trans (ht (by omega)) hlo, ?_⟩
      rwa [show i + 1 + k + 1 = i + (k + 1) + 1 by omega] at hhi

/-- N1. Nonnegativity: basis functions are non-negative. -/
theorem B_nonneg {t : ℕ → ℝ} {i k : ℕ} {x : ℝ}
    (ht : Monotone t) : 0 ≤ B t i k x := by
  revert i
  induction k with
  | zero =>
    intro i
    simp only [B]
    split <;> simp
  | succ k ih =>
    intro i
    simp only [B]
    apply add_nonneg
    · by_cases hB : B t i k x = 0
      · simp [hB]
      · have hpos : 0 < B t i k x := lt_of_le_of_ne (@ih i) (Ne.symm hB)
        have hsupp := B_local_support ht hB
        apply mul_nonneg
        · apply div_nonneg
          · exact sub_nonneg.mpr hsupp.1
          · exact sub_nonneg.mpr (ht (by omega))
        · exact le_of_lt hpos
    · by_cases hB : B t (i + 1) k x = 0
      · simp [hB]
      · have hpos : 0 < B t (i + 1) k x :=
          lt_of_le_of_ne (@ih (i + 1)) (Ne.symm hB)
        have hsupp := B_local_support ht hB
        have hlt : x < t (i + k + 2) := by
          rw [show i + 1 + k + 1 = i + k + 2 by omega] at hsupp
          exact hsupp.2
        apply mul_nonneg
        · apply div_nonneg
          · exact sub_nonneg.mpr (le_of_lt hlt)
          · exact sub_nonneg.mpr (ht (by omega))
        · exact le_of_lt hpos

/-- P1. Partition of unity on `[t k, t (m - k))`. -/
theorem B_partition_of_unity {t : ℕ → ℝ} {m k : ℕ} {x : ℝ}
    (ht : Monotone t) (hk : k < m - k)
    (hlo : t k ≤ x) (hhi : x < t (m - k)) :
    ∑ i ∈ Finset.range (m - k), B t i k x = 1 := by
  induction k generalizing m x with
  | zero =>
    have base : ∀ n : ℕ, 0 < n → t 0 ≤ x → x < t n →
        ∑ i ∈ Finset.range n, B t i 0 x = 1 := by
      intro n
      induction n with
      | zero =>
        intro hn _ _
        omega
      | succ n ihn =>
        intro hn hlo' hhi'
        rw [Finset.sum_range_succ]
        by_cases hxn : x < t n
        · have hBn : B t n 0 x = 0 := by
            simp only [B]
            exact ite_eq_right (fun hcon => lt_irrefl _ (lt_of_le_of_lt hcon.1 hxn))
          rw [hBn, add_zero]
          by_cases hn0 : n = 0
          · subst hn0
            exact absurd hxn (not_lt.mpr hlo')
          · exact ihn (Nat.pos_of_ne_zero hn0) hlo' hxn
        · have hle : t n ≤ x := not_lt.mp hxn
          have hBn : B t n 0 x = 1 := by
            simp only [B]
            exact ite_eq_left ⟨hle, hhi'⟩
          have hsum : ∑ i ∈ Finset.range n, B t i 0 x = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            have hi' : i < n := Finset.mem_range.mp hi
            simp only [B]
            exact ite_eq_right (fun hcon => lt_irrefl _
              (lt_of_lt_of_le hcon.2 (le_trans (ht (by omega)) hle)))
          rw [hBn, hsum, zero_add]
    exact base m hk hlo hhi
  | succ k ih =>
    have hn : m - k = (m - (k + 1)) + 1 := by omega
    have hk' : k < m - k := by omega
    have hlo' : t k ≤ x := le_trans (ht (by omega)) hlo
    have hhi' : x < t (m - k) := lt_of_lt_of_le hhi (ht (by omega))
    have hIH := @ih m x hk' hlo' hhi'
    have key : ∀ j : ℕ, (x - t j) / (t (j + k + 1) - t j) * B t j k x
        + (t (j + k + 1) - x) / (t (j + k + 1) - t j) * B t j k x
        = B t j k x := by
      intro j
      by_cases hden : t (j + k + 1) - t j = 0
      · have hTeq : t (j + k + 1) = t j := by
          have h := hden
          rw [sub_eq_zero] at h
          exact h
        have hc0 : (x - t j) / (t (j + k + 1) - t j) = 0 := by
          rw [hden, div_zero]
        have he0 : (t (j + k + 1) - x) / (t (j + k + 1) - t j) = 0 := by
          rw [hden, div_zero]
        have hB0 : B t j k x = 0 := by
          by_contra hne
          obtain ⟨h1, h2⟩ := B_local_support ht hne
          rw [hTeq] at h2
          exact lt_irrefl _ (lt_of_le_of_lt h1 h2)
        simp [hc0, he0, hB0]
      · have hnum : (x - t j) + (t (j + k + 1) - x)
            = t (j + k + 1) - t j := by
          rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg,
            add_comm (x + -(t j)) (t (j + k + 1) + -x), ← add_assoc,
            add_assoc (t (j + k + 1)) (-x) x, neg_add_cancel, add_zero]
        have hsum : (x - t j) / (t (j + k + 1) - t j)
            + (t (j + k + 1) - x) / (t (j + k + 1) - t j) = 1 := by
          rw [← add_div, hnum, div_self hden]
        rw [← add_mul, hsum, one_mul]
    have hBtop : B t (m - (k + 1)) k x = 0 := by
      by_contra hne
      obtain ⟨h1, h2⟩ := B_local_support ht hne
      exact lt_irrefl _ (lt_of_lt_of_le hhi h1)
    have hBbot : B t 0 k x = 0 := by
      by_contra hne
      obtain ⟨h1, h2⟩ := B_local_support ht hne
      rw [show (0 + k + 1 : ℕ) = k + 1 by omega] at h2
      exact lt_irrefl _ (lt_of_lt_of_le h2 hlo)
    have hcongr : ∑ j ∈ Finset.range (m - k), B t j k x
        = ∑ j ∈ Finset.range (m - k), ((x - t j) / (t (j + k + 1) - t j)
          * B t j k x + (t (j + k + 1) - x) / (t (j + k + 1) - t j)
          * B t j k x) :=
      Finset.sum_congr rfl (fun j _ => (key j).symm)
    rw [hcongr, Finset.sum_add_distrib, hn] at hIH
    have hcs : ∑ j ∈ Finset.range ((m - (k + 1)) + 1),
          (x - t j) / (t (j + k + 1) - t j) * B t j k x
        = (∑ i ∈ Finset.range (m - (k + 1)),
          (x - t i) / (t (i + k + 1) - t i) * B t i k x)
          + (x - t (m - (k + 1)))
          / (t (m - (k + 1) + k + 1) - t (m - (k + 1)))
          * B t (m - (k + 1)) k x :=
      Finset.sum_range_succ _ _
    rw [hcs] at hIH
    have hes : ∑ j ∈ Finset.range ((m - (k + 1)) + 1),
          (t (j + k + 1) - x) / (t (j + k + 1) - t j) * B t j k x
        = (∑ i ∈ Finset.range (m - (k + 1)),
          (t (i + 1 + k + 1) - x) / (t (i + 1 + k + 1) - t (i + 1))
          * B t (i + 1) k x)
          + (t (0 + k + 1) - x) / (t (0 + k + 1) - t 0) * B t 0 k x :=
      Finset.sum_range_succ' _ _
    rw [hes, hBtop, hBbot] at hIH
    simp only [mul_zero, add_zero] at hIH
    have hidx : ∀ i : ℕ, i + k + 2 = i + 1 + k + 1 := fun i => by omega
    simp only [B, hidx]
    rw [Finset.sum_add_distrib]
    exact hIH

/-- Z1a. Repeated knot gives vanishing degree-0 basis. -/
theorem B_zero_of_repeated {t : ℕ → ℝ} {i : ℕ}
    (h : t i = t (i + 1)) : B t i 0 = 0 := by
  funext x
  have hfalse : ¬ (t i ≤ x ∧ x < t (i + 1)) := by
    rw [h]
    exact fun p => lt_irrefl _ (lt_of_le_of_lt p.1 p.2)
  simp only [B, Pi.zero_apply, ite_eq_right hfalse]

/-- Z1b. Empty denominator contributes zero in the recursion. -/
theorem B_empty_denom_left {t : ℕ → ℝ} {i k : ℕ} {x : ℝ}
    (h : t i = t (i + k + 1)) :
    (x - t i) / (t (i + k + 1) - t i) * B t i k x = 0 := by
  have hd : t (i + k + 1) - t i = 0 := by rw [← h, sub_self]
  simp [hd]

end Cslib.Algorithms.Lean.Geometry.BSpline
