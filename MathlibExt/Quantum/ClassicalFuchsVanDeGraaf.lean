/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset

import Mathlib.Tactic.Ring

/-!
# Classical Fuchs-van de Graaf inequalities

For finite classical distributions, the trace distance and
the Bhattacharyya coefficient satisfy
`1 - B ≤ D ≤ sqrt(1 - B ^ 2)`. The quantum operator version
is not included here.
-/

@[expose] public section

/-- Trace distance and Bhattacharyya coefficient for
classical distributions on `Fin n` (QCI-53 core, the
classical Fuchs-van de Graaf inequalities). -/
noncomputable def traceDist {n : ℕ} (p q : Fin n → ℝ) : ℝ :=
  (1 / 2) * ∑ i, |p i - q i|

/-- The Bhattacharyya coefficient `∑ √(p i q i)`. -/
noncomputable def bhatt {n : ℕ} (p q : Fin n → ℝ) : ℝ :=
  ∑ i, Real.sqrt (p i * q i)

private theorem sum_sub_sq {n : ℕ} (p q : Fin n → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    ∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2 = 2 - 2 * bhatt p q := by
  have hpa : ∀ i, (Real.sqrt (p i)) ^ 2 = p i := fun i => Real.sq_sqrt (hp0 i)
  have hqa : ∀ i, (Real.sqrt (q i)) ^ 2 = q i := fun i => Real.sq_sqrt (hq0 i)
  have hsq : ∀ i, Real.sqrt (p i * q i) = Real.sqrt (p i) * Real.sqrt (q i) :=
    fun i => Real.sqrt_mul (hp0 i) _
  have e : ∀ i : Fin n, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2 =
      p i - 2 * (Real.sqrt (p i) * Real.sqrt (q i)) + q i := by
    intro i
    have h : (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2
        = (Real.sqrt (p i)) ^ 2 - 2 * (Real.sqrt (p i) * Real.sqrt (q i))
          + (Real.sqrt (q i)) ^ 2 := by ring
    rw [h, hpa i, hqa i]
  have hB : ∑ i, (Real.sqrt (p i) * Real.sqrt (q i)) = bhatt p q := by
    unfold bhatt
    exact Finset.sum_congr rfl (fun i _ => (hsq i).symm)
  have h2 : ∑ i, (2 * (Real.sqrt (p i) * Real.sqrt (q i))) = 2 * bhatt p q := by
    rw [← Finset.mul_sum, hB]
  calc ∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2
      = ∑ i, (p i - 2 * (Real.sqrt (p i) * Real.sqrt (q i)) + q i) :=
        Finset.sum_congr rfl (fun i _ => e i)
    _ = (∑ i, p i) - (∑ i, (2 * (Real.sqrt (p i) * Real.sqrt (q i))))
        + (∑ i, q i) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = 2 - 2 * bhatt p q := by rw [hp1, hq1, h2]; ring

private theorem sum_add_sq {n : ℕ} (p q : Fin n → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    ∑ i, (Real.sqrt (p i) + Real.sqrt (q i)) ^ 2 = 2 + 2 * bhatt p q := by
  have hpa : ∀ i, (Real.sqrt (p i)) ^ 2 = p i := fun i => Real.sq_sqrt (hp0 i)
  have hqa : ∀ i, (Real.sqrt (q i)) ^ 2 = q i := fun i => Real.sq_sqrt (hq0 i)
  have hsq : ∀ i, Real.sqrt (p i * q i) = Real.sqrt (p i) * Real.sqrt (q i) :=
    fun i => Real.sqrt_mul (hp0 i) _
  have e : ∀ i : Fin n, (Real.sqrt (p i) + Real.sqrt (q i)) ^ 2 =
      p i + 2 * (Real.sqrt (p i) * Real.sqrt (q i)) + q i := by
    intro i
    have h : (Real.sqrt (p i) + Real.sqrt (q i)) ^ 2
        = (Real.sqrt (p i)) ^ 2 + 2 * (Real.sqrt (p i) * Real.sqrt (q i))
          + (Real.sqrt (q i)) ^ 2 := by ring
    rw [h, hpa i, hqa i]
  have hB : ∑ i, (Real.sqrt (p i) * Real.sqrt (q i)) = bhatt p q := by
    unfold bhatt
    exact Finset.sum_congr rfl (fun i _ => (hsq i).symm)
  have h2 : ∑ i, (2 * (Real.sqrt (p i) * Real.sqrt (q i))) = 2 * bhatt p q := by
    rw [← Finset.mul_sum, hB]
  calc ∑ i, (Real.sqrt (p i) + Real.sqrt (q i)) ^ 2
      = ∑ i, (p i + 2 * (Real.sqrt (p i) * Real.sqrt (q i)) + q i) :=
        Finset.sum_congr rfl (fun i _ => e i)
    _ = (∑ i, p i) + (∑ i, (2 * (Real.sqrt (p i) * Real.sqrt (q i))))
        + (∑ i, q i) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = 2 + 2 * bhatt p q := by rw [hp1, hq1, h2]; ring

private theorem abs_sub_eq {n : ℕ} (p q : Fin n → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i) (i : Fin n) :
    |p i - q i|
      = |Real.sqrt (p i) - Real.sqrt (q i)|
        * (Real.sqrt (p i) + Real.sqrt (q i)) := by
  have hpa : (Real.sqrt (p i)) ^ 2 = p i := Real.sq_sqrt (hp0 i)
  have hqa : (Real.sqrt (q i)) ^ 2 = q i := Real.sq_sqrt (hq0 i)
  have hnonneg : 0 ≤ Real.sqrt (p i) + Real.sqrt (q i) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hfac : p i - q i =
      (Real.sqrt (p i) - Real.sqrt (q i))
        * (Real.sqrt (p i) + Real.sqrt (q i)) := by
    have h : (Real.sqrt (p i) - Real.sqrt (q i))
          * (Real.sqrt (p i) + Real.sqrt (q i))
        = (Real.sqrt (p i)) ^ 2 - (Real.sqrt (q i)) ^ 2 := by ring
    rw [h, hpa, hqa]
  rw [hfac, abs_mul, abs_of_nonneg hnonneg]

/-- Lower bound: `1 - B ≤ D`. -/
theorem one_sub_bhatt_le_traceDist {n : ℕ} (p q : Fin n → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    1 - bhatt p q ≤ traceDist p q := by
  have hpt : ∀ i : Fin n,
      (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2 ≤ |p i - q i| := by
    intro i
    have ha0 := Real.sqrt_nonneg (p i)
    have hb0 := Real.sqrt_nonneg (q i)
    have hle : |Real.sqrt (p i) - Real.sqrt (q i)|
        ≤ Real.sqrt (p i) + Real.sqrt (q i) := by
      by_cases h : Real.sqrt (p i) ≤ Real.sqrt (q i)
      · rw [abs_of_nonpos (sub_nonpos.mpr h)]
        linarith
      · push Not at h
        rw [abs_of_nonneg (sub_nonneg.mpr (le_of_lt h))]
        linarith
    have hsq2 : (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2
        = |Real.sqrt (p i) - Real.sqrt (q i)|
          * |Real.sqrt (p i) - Real.sqrt (q i)| := by
      rw [← sq_abs]
      ring
    rw [abs_sub_eq p q hp0 hq0 i, hsq2]
    exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)
  have hsum : ∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2
      ≤ ∑ i, |p i - q i| :=
    Finset.sum_le_sum (fun i _ => hpt i)
  have hS : 2 - 2 * bhatt p q ≤ ∑ i, |p i - q i| := by
    have h := sum_sub_sq p q hp0 hq0 hp1 hq1
    linarith
  unfold traceDist
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hmul := mul_le_mul_of_nonneg_left hS hhalf
  linarith

/-- Upper bound: `D ≤ √(1 - B²)`. -/
theorem traceDist_le_sqrt {n : ℕ} (p q : Fin n → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    traceDist p q ≤ Real.sqrt (1 - (bhatt p q) ^ 2) := by
  have hcs : (∑ i, (|Real.sqrt (p i) - Real.sqrt (q i)|
        * (Real.sqrt (p i) + Real.sqrt (q i)))) ^ 2
      ≤ (∑ i, (|Real.sqrt (p i) - Real.sqrt (q i)|) ^ 2)
        * (∑ i, (Real.sqrt (p i) + Real.sqrt (q i)) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have e1 : ∑ i, (|Real.sqrt (p i) - Real.sqrt (q i)|
        * (Real.sqrt (p i) + Real.sqrt (q i)))
      = ∑ i, |p i - q i| :=
    Finset.sum_congr rfl (fun i _ => (abs_sub_eq p q hp0 hq0 i).symm)
  have e2 : ∑ i, (|Real.sqrt (p i) - Real.sqrt (q i)|) ^ 2
      = 2 - 2 * bhatt p q := by
    have h : ∑ i, (|Real.sqrt (p i) - Real.sqrt (q i)|) ^ 2
        = ∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2 :=
      Finset.sum_congr rfl (fun i _ => sq_abs _)
    rw [h]
    exact sum_sub_sq p q hp0 hq0 hp1 hq1
  have e3 : ∑ i, (Real.sqrt (p i) + Real.sqrt (q i)) ^ 2
      = 2 + 2 * bhatt p q :=
    sum_add_sq p q hp0 hq0 hp1 hq1
  rw [e1, e2, e3] at hcs
  have hcs' : (∑ i, |p i - q i|) ^ 2 ≤ 4 * (1 - (bhatt p q) ^ 2) := by
    calc (∑ i, |p i - q i|) ^ 2
        ≤ (2 - 2 * bhatt p q) * (2 + 2 * bhatt p q) := hcs
      _ = 4 * (1 - (bhatt p q) ^ 2) := by ring
  have hfin : (traceDist p q) ^ 2 ≤ 1 - (bhatt p q) ^ 2 := by
    have hsqT : (traceDist p q) ^ 2 = ((∑ i, |p i - q i|) ^ 2) / 4 := by
      unfold traceDist
      ring
    rw [hsqT]
    linarith [hcs']
  exact Real.le_sqrt_of_sq_le hfin

end
