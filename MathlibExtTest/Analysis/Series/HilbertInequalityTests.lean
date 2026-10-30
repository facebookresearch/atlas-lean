/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Series.HilbertInequality
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Tests for Hilbert's inequality

* The row sum at `m = 0` is at most `π`.
* The `2 × 2` block of the Hilbert kernel sums to `17 / 12`, and the
  finite Hilbert bound gives `17 / 12 ≤ 2π`.
* The indicator sequence `δ₀` gives the clean instance `1 / 2 ≤ π`.
* The geometric sequence `(1 / 2) ^ n` gives the instance with
  `∑' (a n) ^ 2 = 4 / 3`.
-/

namespace MathlibExtTest.Analysis.Series.HilbertInequalityTests

open MathlibExt.Analysis.Series.HilbertInequality

/-- The row sum at `m = 0` is at most `π`. -/
example : ∑' (n : ℕ), hilbertKernel 0 n * (Real.sqrt ((n:ℝ) + 1))⁻¹ ≤ Real.pi := by
  have h := hilbertKernel_row_sum_le 0
  simpa using h

/-- The `2 × 2` block of the Hilbert kernel sums to `17 / 12`. -/
example : ∑ m ∈ Finset.range 2, ∑ n ∈ Finset.range 2,
    (1:ℝ) * 1 / ((m:ℝ) + n + 2) = 17 / 12 := by
  norm_num [Finset.sum_range_succ]

/-- The finite Hilbert bound, computed: `17 / 12 ≤ 2π`. -/
example : (17:ℝ) / 12 ≤ Real.pi * 2 := by
  have h := hilbert_inequality_finite (N := 2) (a := fun _ => (1:ℝ)) (b := fun _ => (1:ℝ))
    (fun _ => zero_le_one) (fun _ => zero_le_one)
  simp only [Finset.sum_range_succ] at h
  norm_num at h
  have hsqrt : Real.pi * Real.sqrt (2:ℝ) * Real.sqrt (2:ℝ) = Real.pi * 2 := by
    rw [mul_assoc, ← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2),
      show (2:ℝ) * 2 = 2 ^ 2 by ring, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  rw [hsqrt] at h
  exact h

/-- The indicator sequence `δ₀` gives the clean instance `1 / 2 ≤ π`. -/
example : (1:ℝ) / 2 ≤ Real.pi := by
  set a : ℕ → ℝ := fun n => if n = 0 then (1:ℝ) else 0 with ha_def
  have ha : Summable (fun n => (a n) ^ 2) := by
    have h : (fun n : ℕ => (a n) ^ 2) = a := by
      funext n
      by_cases hn : n = 0 <;> simp [ha_def, hn]
    rw [h]
    exact summable_of_ne_finset_zero (s := {0}) (by
      intro n hn
      have hne : n ≠ 0 := Finset.notMem_singleton.mp hn
      simp [ha_def, hne])
  have hsum : ∑' (n : ℕ), (a n) ^ 2 = 1 := by
    have h : (fun n : ℕ => (a n) ^ 2) = a := by
      funext n
      by_cases hn : n = 0 <;> simp [ha_def, hn]
    rw [h, ha_def]
    exact tsum_ite_eq 0 (fun _ => (1:ℝ))
  have hmain := hilbert_inequality ha ha
  have hL : ∑' (p : ℕ × ℕ), |a p.1 * a p.2| * hilbertKernel p.1 p.2 = 1 / 2 := by
    have h0 : ∑' (p : ℕ × ℕ), |a p.1 * a p.2| * hilbertKernel p.1 p.2 =
        |a 0 * a 0| * hilbertKernel 0 0 := by
      apply tsum_eq_single (0, 0)
      intro p hp
      by_cases h1 : p.1 = 0
      · have h2 : p.2 ≠ 0 := fun h => hp (Prod.ext h1 h)
        simp [ha_def, h1, h2]
      · simp [ha_def, h1]
    rw [h0]
    norm_num [ha_def, hilbertKernel]
  rw [hL, hsum] at hmain
  simpa using hmain

/-- The geometric sequence `(1 / 2) ^ n` is square-summable with
`∑' (a n) ^ 2 = 4 / 3`, and Hilbert's inequality gives the bound
`∑' (p), |(1/2) ^ p.1 * (1/2) ^ p.2| * hilbertKernel p.1 p.2 ≤ π * 4 / 3`. -/
example : ∑' (p : ℕ × ℕ), |(1 / 2 : ℝ) ^ p.1 * (1 / 2 : ℝ) ^ p.2| *
    hilbertKernel p.1 p.2 ≤ Real.pi * (4 / 3) := by
  have ha : Summable (fun n : ℕ => (((1 / 2 : ℝ) ^ n) ^ 2)) := by
    have h : (fun n : ℕ => (((1 / 2 : ℝ) ^ n) ^ 2)) = fun n : ℕ => (1 / 4 : ℝ) ^ n := by
      funext n
      rw [← pow_mul, mul_comm n 2, pow_mul]
      norm_num
    rw [h]
    exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsum : ∑' (n : ℕ), (((1 / 2 : ℝ) ^ n) ^ 2) = 4 / 3 := by
    have h : (fun n : ℕ => (((1 / 2 : ℝ) ^ n) ^ 2)) = fun n : ℕ => (1 / 4 : ℝ) ^ n := by
      funext n
      rw [← pow_mul, mul_comm n 2, pow_mul]
      norm_num
    rw [h, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  have hmain := hilbert_inequality ha ha
  rw [hsum] at hmain
  have hsqrt : Real.sqrt (4 / 3 : ℝ) * Real.sqrt (4 / 3 : ℝ) = 4 / 3 :=
    Real.mul_self_sqrt (by norm_num)
  calc ∑' (p : ℕ × ℕ), |(1 / 2 : ℝ) ^ p.1 * (1 / 2 : ℝ) ^ p.2| *
          hilbertKernel p.1 p.2
      ≤ Real.pi * Real.sqrt (4 / 3 : ℝ) * Real.sqrt (4 / 3 : ℝ) := hmain
    _ = Real.pi * (4 / 3) := by rw [mul_assoc, hsqrt]

end MathlibExtTest.Analysis.Series.HilbertInequalityTests

namespace MathlibExtTest.Analysis.Series.HilbertInequalityTests

open MathlibExt.Analysis.Series.HilbertInequality

/-- The infinite nonzero geometric Hilbert family is summable, as well as bounded. -/
theorem geometric_hilbert_terms_summable :
    Summable (fun p : ℕ × ℕ => |(1 / 2 : ℝ) ^ p.1 * (1 / 2 : ℝ) ^ p.2| *
      hilbertKernel p.1 p.2) := by
  have hsquare : Summable (fun n : ℕ => (((1 / 2 : ℝ) ^ n) ^ 2)) := by
    have h : (fun n : ℕ => (((1 / 2 : ℝ) ^ n) ^ 2)) = fun n : ℕ => (1 / 4 : ℝ) ^ n := by
      funext n
      rw [← pow_mul, mul_comm n 2, pow_mul]
      norm_num
    rw [h]
    exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  exact summable_hilbert_terms hsquare hsquare

end MathlibExtTest.Analysis.Series.HilbertInequalityTests
