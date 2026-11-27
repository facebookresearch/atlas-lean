/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Algorithms.Networking.Aimd
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

/-!
# Sharp bounds for Jain's fairness index

For a nonzero allocation of nonnegative loads, `fairness` ranges from `1 / n`
(one positive share) to `1` (all shares equal). More generally, if `k ≥ 1` users each receive
the same positive share and all other users receive zero, the index is
`k / n`. The index is continuous on its domain; `fairness_scale` gives
independence of the unit in which loads are measured.

D.-M. Chiu and R. Jain, “Analysis of the increase and decrease algorithms for
congestion avoidance in computer networks”, *Computer Networks and ISDN Systems*
17 (1989), 1–14, §1.4(a)–(d), p. 5. The sharp lower bound and the two equality
characterizations are deductions from the displayed index.
-/

public section

namespace Cslib.Algorithms.Networking.Aimd

open Finset

variable {n : ℕ} {x : Fin n → ℝ}

private theorem sum_sq_pos_of_ne_zero (hx₀ : x ≠ 0) : 0 < ∑ i, x i ^ 2 := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    contrapose! hx₀
    exact funext hx₀
  exact Finset.sum_pos' (fun j _ => sq_nonneg (x j)) ⟨i, mem_univ i, sq_pos_of_ne_zero hi⟩

/-- For `n > 0` users with nonnegative loads not all zero, Jain's fairness
index lies in the closed interval from `1 / n` to `1`. -/
theorem fairness_mem_Icc_one_div (hn : 0 < n) (hx : ∀ i, 0 ≤ x i) (hx₀ : x ≠ 0) :
    fairness x ∈ Set.Icc (1 / (n : ℝ)) 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hq := sum_sq_pos_of_ne_zero hx₀
  constructor
  · rw [fairness, div_le_div_iff₀ hn' (mul_pos hn' hq), one_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (sum_sq_le_sq_sum_of_nonneg (fun i _ => hx i)) hn'.le
  · rw [fairness, div_le_one (mul_pos hn' hq)]
    simpa using sq_sum_le_card_mul_sum_sq (s := univ) (f := x)

/-- If precisely the users in a nonempty set `s` receive a common positive
share `c`, and all others receive zero, their fairness index is `s.card / n`. -/
theorem fairness_eq_card_div_of_equal_shares (s : Finset (Fin n)) (hs : s.Nonempty)
    {c : ℝ} (hc : 0 < c) :
    fairness (fun i => if i ∈ s then c else 0) = (s.card : ℝ) / n := by
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hunit : ∑ i, (if i ∈ s then (1 : ℝ) else 0) ^ 2 = s.card := by
    simp [ite_pow]
  have hscale := fairness_scale (fun i => if i ∈ s then (1 : ℝ) else 0) hc (hunit ▸ hcard.ne')
  simpa only [mul_ite, mul_one, mul_zero] using hscale.trans (by
    rw [fairness, hunit]
    simp [sq, mul_div_mul_right, hcard.ne'])

/-- For `n > 0` users with nonnegative loads not all zero, Jain's fairness
index is `1 / n` if and only if exactly one user has a positive load. -/
theorem fairness_eq_one_div_iff (hn : 0 < n) (hx : ∀ i, 0 ≤ x i) (hx₀ : x ≠ 0) :
    fairness x = 1 / (n : ℝ) ↔ ∃! i, 0 < x i := by
  constructor
  · intro h
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have heq := (div_eq_div_iff (mul_ne_zero hn' (sum_sq_pos_of_ne_zero hx₀).ne') hn').mp h
    rw [one_mul, mul_comm (n : ℝ)] at heq
    have hle (i : Fin n) (_ : i ∈ univ) : x i * x i ≤ x i * ∑ j, x j :=
      mul_le_mul_of_nonneg_left (single_le_sum (fun j _ => hx j) (mem_univ i)) (hx i)
    have hall := (sum_eq_sum_iff_of_le hle).mp (by
      simpa only [← sq, ← sum_mul] using (mul_right_cancel₀ hn' heq).symm)
    obtain ⟨i, hi⟩ : ∃ i, 0 < x i := by
      contrapose! hx₀
      exact funext fun i => le_antisymm (hx₀ i) (hx i)
    refine ⟨i, hi, fun j hj => ?_⟩
    by_contra hji
    have hlt := single_lt_sum hji (mem_univ i) (mem_univ j) hj (fun k _ _ => hx k)
    exact hlt.ne (mul_left_cancel₀ hi.ne' (hall i (mem_univ i)))
  · rintro ⟨i, hi, hu⟩
    have h : x = fun j => if j ∈ ({i} : Finset (Fin n)) then x i else 0 := by
      funext j
      by_cases hji : j = i
      · simp [hji]
      · simpa [hji] using le_antisymm (le_of_not_gt (fun hj => hji (hu j hj))) (hx j)
    rw [h]
    simpa using fairness_eq_card_div_of_equal_shares {i} (singleton_nonempty i) hi

/-- For a nonzero vector of `n > 0` real loads, Jain's fairness index is `1`
if and only if all loads are equal. This equivalence does not require nonnegativity. -/
theorem fairness_eq_one_iff (hn : 0 < n) (hx₀ : x ≠ 0) :
    fairness x = 1 ↔ ∀ i j, x i = x j := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h := (even_two.strictConvexOn_pow (by decide)).map_sum_eq_iff_of_pos
    (t := univ) (w := fun _ : Fin n => (n : ℝ)⁻¹) (p := x)
    (fun _ _ => inv_pos.mpr hn') (by simp [nsmul_eq_mul, hn'.ne']) (by simp)
  simp only [smul_eq_mul, ← mul_sum, mem_univ, true_implies] at h
  rw [← h, fairness, div_eq_one_iff_eq (mul_ne_zero hn'.ne' (sum_sq_pos_of_ne_zero hx₀).ne')]
  field_simp

/-- For `n > 0`, Jain's fairness index is continuous on the nonnegative
allocations other than the zero vector, with the product topology on loads. -/
theorem continuousOn_fairness (hn : 0 < n) :
    ContinuousOn (fairness (n := n)) {x | (∀ i, 0 ≤ x i) ∧ x ≠ 0} := by
  unfold fairness
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro x hx
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hn.ne') (sum_sq_pos_of_ne_zero hx.2).ne'

end Cslib.Algorithms.Networking.Aimd
