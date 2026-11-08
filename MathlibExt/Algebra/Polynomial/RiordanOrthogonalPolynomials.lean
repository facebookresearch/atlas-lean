/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Algebra.Polynomial.FormalOrthogonality
public import MathlibExt.LinearAlgebra.Matrix.StieltjesMatrix
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Inverse
import MathlibExt.Algebra.Polynomial.FavardIff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

@[expose] public section

section
namespace MetaMathlibExt

/-- A Riordan array with `coeff 0 h = 0` is lower-triangular. -/
private theorem riordan_L_triangular (d h : PowerSeries ℝ) (L : ℕ → ℕ → ℝ)
    (h0 : PowerSeries.coeff 0 h = 0)
    (hL : ∀ n k : ℕ, L n k = PowerSeries.coeff n (d * h ^ k))
    (n k : ℕ) (hk : n < k) : L n k = 0 := by
  rw [hL n k]
  have hX : (PowerSeries.X : PowerSeries ℝ) ∣ h := by
    rw [PowerSeries.X_dvd_iff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact h0
  have hXk : (PowerSeries.X : PowerSeries ℝ) ^ k ∣ h ^ k :=
    pow_dvd_pow_of_dvd hX k
  have hdvd : (PowerSeries.X : PowerSeries ℝ) ^ k ∣ d * h ^ k :=
    Dvd.dvd.mul_left hXk d
  rw [PowerSeries.X_pow_dvd_iff] at hdvd
  exact hdvd n hk

/-- A monic polynomial of nat-degree `n` has `n`-th coefficient `1`. -/
private theorem monic_coeff_eq_one (P : Polynomial ℝ) (n : ℕ)
    (hm : P.Monic) (hd : P.natDegree = n) : P.coeff n = 1 := by
  have h := hm.leadingCoeff
  unfold Polynomial.leadingCoeff at h
  rw [hd] at h
  exact h

/-- Values of the Stieltjes production matrix at the corner positions. -/
private theorem stieltjes_zero_one (a1 b1 a b : ℝ) :
    stieltjesMatrix a1 b1 a b 0 1 = 1 := by
  simp [stieltjesMatrix]

private theorem stieltjes_zero_zero (a1 b1 a b : ℝ) :
    stieltjesMatrix a1 b1 a b 0 0 = a1 := by
  simp [stieltjesMatrix]

private theorem stieltjes_one_zero (a1 b1 a b : ℝ) :
    stieltjesMatrix a1 b1 a b 1 0 = b1 := by
  simp [stieltjesMatrix]

/-- Coefficient shift for multiplication by `X` on the right. -/
private theorem coeff_mul_X (F : PowerSeries ℝ) (N : ℕ) :
    PowerSeries.coeff N (F * PowerSeries.X) =
      (if 1 ≤ N then PowerSeries.coeff (N - 1) F else 0) := by
  rw [mul_comm F PowerSeries.X]
  cases N with
  | zero =>
    rw [PowerSeries.coeff_zero_X_mul]
    rw [ite_eq_right (by omega : ¬ 1 ≤ 0)]
  | succ m =>
    rw [PowerSeries.coeff_succ_X_mul]
    rw [ite_eq_left (by omega : 1 ≤ m + 1)]
    have hm : m + 1 - 1 = m := by omega
    rw [hm]

/-- Coefficient shift for multiplication by `X ^ 2` on the right. -/
private theorem coeff_mul_X_pow_two (F : PowerSeries ℝ) (N : ℕ) :
    PowerSeries.coeff N (F * PowerSeries.X ^ 2) =
      (if 2 ≤ N then PowerSeries.coeff (N - 2) F else 0) := by
  have hEq : F * PowerSeries.X ^ 2 =
      PowerSeries.X * (PowerSeries.X * F) := by ring
  rw [hEq]
  cases N with
  | zero =>
    rw [PowerSeries.coeff_zero_X_mul]
    rw [ite_eq_right (by omega : ¬ 2 ≤ 0)]
  | succ m =>
    cases m with
    | zero =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_X_mul]
      rw [ite_eq_right (by omega : ¬ 2 ≤ 1)]
    | succ k =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul]
      rw [ite_eq_left (by omega : 2 ≤ k + 1 + 1)]
      have hk : k + 1 + 1 - 2 = k := by omega
      rw [hk]

/-- Coefficients of `1 - C lam * X - C mu * X ^ 2`. -/
private theorem coeff_one_sub (lam mu : ℝ) (N : ℕ) :
    PowerSeries.coeff N
        (1 - PowerSeries.C lam * PowerSeries.X -
          PowerSeries.C mu * PowerSeries.X ^ 2) =
      (if N = 0 then 1 else if N = 1 then -lam else if N = 2 then -mu else 0) := by
  have h1 : PowerSeries.coeff N (1 : PowerSeries ℝ) =
      (if N = 0 then 1 else 0) := by
    rw [PowerSeries.coeff_one]
  have hX : PowerSeries.coeff N (PowerSeries.C lam * PowerSeries.X) =
      (if N = 1 then lam else 0) := by
    rw [PowerSeries.coeff_C_mul]
    have hXN : PowerSeries.coeff N (PowerSeries.X : PowerSeries ℝ) =
        (if N = 1 then 1 else 0) := by
      cases N with
      | zero =>
        have hX0 : (PowerSeries.X : PowerSeries ℝ) =
            PowerSeries.X * 1 := by rw [mul_one]
        rw [hX0, PowerSeries.coeff_zero_X_mul]
        rw [ite_eq_right (by omega : ¬ 0 = 1)]
      | succ m =>
        cases m with
        | zero =>
          have hX1 : (PowerSeries.X : PowerSeries ℝ) =
              PowerSeries.X * 1 := by rw [mul_one]
          rw [hX1, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one]
          rw [ite_eq_left rfl, ite_eq_left rfl]
        | succ k =>
          have hXk : (PowerSeries.X : PowerSeries ℝ) =
              PowerSeries.X * 1 := by rw [mul_one]
          rw [hXk, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one]
          rw [ite_eq_right (by omega : ¬ k + 1 = 0)]
          rw [ite_eq_right (by omega : ¬ k + 1 + 1 = 1)]
    rw [hXN]
    by_cases hN : N = 1
    · rw [ite_eq_left hN, ite_eq_left hN, mul_one]
    · rw [ite_eq_right hN, ite_eq_right hN, mul_zero]
  have hX2 : PowerSeries.coeff N (PowerSeries.C mu * PowerSeries.X ^ 2) =
      (if N = 2 then mu else 0) := by
    rw [PowerSeries.coeff_C_mul]
    have hX2N : PowerSeries.coeff N ((PowerSeries.X : PowerSeries ℝ) ^ 2) =
        (if N = 2 then 1 else 0) := by
      have hEq : ((PowerSeries.X : PowerSeries ℝ) ^ 2) =
          PowerSeries.X * (PowerSeries.X * 1) := by rw [mul_one]; ring
      rw [hEq]
      cases N with
      | zero =>
        rw [PowerSeries.coeff_zero_X_mul]
        rw [ite_eq_right (by omega : ¬ 0 = 2)]
      | succ m =>
        cases m with
        | zero =>
          rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_X_mul]
          rw [ite_eq_right (by omega : ¬ 1 = 2)]
        | succ k =>
          cases k with
          | zero =>
            rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul,
              PowerSeries.coeff_one]
            rw [ite_eq_left rfl, ite_eq_left rfl]
          | succ j =>
            rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul,
              PowerSeries.coeff_one]
            rw [ite_eq_right (by omega : ¬ j + 1 = 0)]
            rw [ite_eq_right (by omega : ¬ j + 1 + 1 + 1 = 2)]
    rw [hX2N]
    by_cases hN : N = 2
    · rw [ite_eq_left hN, ite_eq_left hN, mul_one]
    · rw [ite_eq_right hN, ite_eq_right hN, mul_zero]
  rw [map_sub, map_sub, h1, hX, hX2]
  by_cases hN0 : N = 0
  · rw [ite_eq_left hN0, ite_eq_right (by omega : ¬ N = 1),
      ite_eq_right (by omega : ¬ N = 2)]
    rw [ite_eq_left hN0]
    ring
  · rw [ite_eq_right hN0]
    by_cases hN1 : N = 1
    · rw [ite_eq_left hN1, ite_eq_right (by omega : ¬ N = 2)]
      rw [ite_eq_right hN0, ite_eq_left hN1]
      ring
    · rw [ite_eq_right hN1]
      by_cases hN2 : N = 2
      · rw [ite_eq_left hN2]
        rw [ite_eq_right hN0, ite_eq_right hN1, ite_eq_left hN2]
        ring
      · rw [ite_eq_right hN2]
        rw [ite_eq_right hN0, ite_eq_right hN1, ite_eq_right hN2]
        ring

/-- Meixner power-series form implies the coefficient recurrence. -/
private theorem meixner_to_recurrence (d h : PowerSeries ℝ) (L : ℕ → ℕ → ℝ)
    (hL : ∀ n k : ℕ, L n k = PowerSeries.coeff n (d * h ^ k))
    (lam mu r s : ℝ)
    (hd : d * (1 + PowerSeries.C r * PowerSeries.X +
        PowerSeries.C s * PowerSeries.X ^ 2) =
      1 - PowerSeries.C lam * PowerSeries.X -
        PowerSeries.C mu * PowerSeries.X ^ 2)
    (hh : h * (1 + PowerSeries.C r * PowerSeries.X +
        PowerSeries.C s * PowerSeries.X ^ 2) =
      PowerSeries.X) :
    ∀ N K : ℕ,
      L N K + r * (if 1 ≤ N then L (N - 1) K else 0) -
          (if 1 ≤ N ∧ 1 ≤ K then L (N - 1) (K - 1) else 0) +
          s * (if 2 ≤ N then L (N - 2) K else 0) =
        (if K = 0 then
          if N = 0 then 1 else if N = 1 then -lam else if N = 2 then -mu else 0
        else 0) := by
  intro N K
  cases K with
  | zero =>
    have hMid : (if 1 ≤ N ∧ 1 ≤ 0 then L (N - 1) (0 - 1) else 0) = 0 := by
      rw [ite_eq_right (by omega : ¬ (1 ≤ N ∧ 1 ≤ 0))]
    rw [hMid, sub_zero]
    rw [ite_eq_left rfl]
    have hExpand : d * (1 + PowerSeries.C r * PowerSeries.X +
          PowerSeries.C s * PowerSeries.X ^ 2) =
        d + PowerSeries.C r * (d * PowerSeries.X) +
          PowerSeries.C s * (d * PowerSeries.X ^ 2) := by ring
    rw [hExpand] at hd
    have hCoeff := congrArg (PowerSeries.coeff N) hd
    rw [map_add, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
      coeff_one_sub lam mu N] at hCoeff
    rw [hL N 0, pow_zero, mul_one]
    rw [coeff_mul_X d N, coeff_mul_X_pow_two d N] at hCoeff
    have e1 : (if 1 ≤ N then PowerSeries.coeff (N - 1) d else 0) =
        (if 1 ≤ N then L (N - 1) 0 else 0) := by
      by_cases hN : 1 ≤ N
      · rw [ite_eq_left hN, ite_eq_left hN, hL (N - 1) 0, pow_zero, mul_one]
      · rw [ite_eq_right hN, ite_eq_right hN]
    have e2 : (if 2 ≤ N then PowerSeries.coeff (N - 2) d else 0) =
        (if 2 ≤ N then L (N - 2) 0 else 0) := by
      by_cases hN : 2 ≤ N
      · rw [ite_eq_left hN, ite_eq_left hN, hL (N - 2) 0, pow_zero, mul_one]
      · rw [ite_eq_right hN, ite_eq_right hN]
    rw [e1, e2] at hCoeff
    linarith [hCoeff]
  | succ j =>
    have hK : (if j + 1 = 0 then
        (if N = 0 then (1 : ℝ) else if N = 1 then -lam else if N = 2 then -mu else 0)
        else 0) = 0 := by
      rw [ite_eq_right (by omega : ¬ j + 1 = 0)]
    rw [hK]
    have hMid : (if 1 ≤ N ∧ 1 ≤ j + 1 then L (N - 1) (j + 1 - 1) else 0) =
        (if 1 ≤ N then L (N - 1) j else 0) := by
      by_cases hN : 1 ≤ N
      · rw [ite_eq_left ⟨hN, by omega⟩, ite_eq_left hN]
        have hj : j + 1 - 1 = j := by omega
        rw [hj]
      · rw [ite_eq_right (by omega : ¬ (1 ≤ N ∧ 1 ≤ j + 1)),
          ite_eq_right hN]
    rw [hMid]
    have hMul : d * h ^ (j + 1) * (1 + PowerSeries.C r * PowerSeries.X +
          PowerSeries.C s * PowerSeries.X ^ 2) =
        PowerSeries.X * (d * h ^ j) := by
      have hPow : h ^ (j + 1) = h ^ j * h := by rw [pow_succ]
      rw [hPow]
      linear_combination (d * h ^ j) * hh
    have hExpand : d * h ^ (j + 1) * (1 + PowerSeries.C r * PowerSeries.X +
          PowerSeries.C s * PowerSeries.X ^ 2) =
        d * h ^ (j + 1) + PowerSeries.C r * ((d * h ^ (j + 1)) * PowerSeries.X) +
          PowerSeries.C s * ((d * h ^ (j + 1)) * PowerSeries.X ^ 2) := by ring
    rw [hExpand] at hMul
    have hCoeff := congrArg (PowerSeries.coeff N) hMul
    rw [map_add, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul] at hCoeff
    have hRhs : PowerSeries.coeff N (PowerSeries.X * (d * h ^ j)) =
        (if 1 ≤ N then L (N - 1) j else 0) := by
      cases N with
      | zero =>
        rw [PowerSeries.coeff_zero_X_mul]
        rw [ite_eq_right (by omega : ¬ 1 ≤ 0)]
      | succ m =>
        rw [PowerSeries.coeff_succ_X_mul]
        rw [ite_eq_left (by omega : 1 ≤ m + 1)]
        have hm : m + 1 - 1 = m := by omega
        rw [hm, hL m j]
    rw [hRhs] at hCoeff
    rw [coeff_mul_X (d * h ^ (j + 1)) N,
      coeff_mul_X_pow_two (d * h ^ (j + 1)) N] at hCoeff
    have e1 : (if 1 ≤ N then PowerSeries.coeff (N - 1) (d * h ^ (j + 1)) else 0) =
        (if 1 ≤ N then L (N - 1) (j + 1) else 0) := by
      by_cases hN : 1 ≤ N
      · rw [ite_eq_left hN, ite_eq_left hN, hL (N - 1) (j + 1)]
      · rw [ite_eq_right hN, ite_eq_right hN]
    have e2 : (if 2 ≤ N then PowerSeries.coeff (N - 2) (d * h ^ (j + 1)) else 0) =
        (if 2 ≤ N then L (N - 2) (j + 1) else 0) := by
      by_cases hN : 2 ≤ N
      · rw [ite_eq_left hN, ite_eq_left hN, hL (N - 2) (j + 1)]
      · rw [ite_eq_right hN, ite_eq_right hN]
    rw [e1, e2] at hCoeff
    have hLN : L N (j + 1) = PowerSeries.coeff N (d * h ^ (j + 1)) := hL N (j + 1)
    rw [hLN]
    linarith [hCoeff]

/-- Coefficient recurrence implies the Meixner power-series form. -/
private theorem recurrence_to_meixner (d h : PowerSeries ℝ) (L : ℕ → ℕ → ℝ)
    (hL : ∀ n k : ℕ, L n k = PowerSeries.coeff n (d * h ^ k))
    (hd0 : PowerSeries.coeff 0 d ≠ 0)
    (lam mu r s : ℝ)
    (hRec : ∀ N K : ℕ,
      L N K + r * (if 1 ≤ N then L (N - 1) K else 0) -
          (if 1 ≤ N ∧ 1 ≤ K then L (N - 1) (K - 1) else 0) +
          s * (if 2 ≤ N then L (N - 2) K else 0) =
        (if K = 0 then
          if N = 0 then 1 else if N = 1 then -lam else if N = 2 then -mu else 0
        else 0)) :
    d * (1 + PowerSeries.C r * PowerSeries.X +
        PowerSeries.C s * PowerSeries.X ^ 2) =
      1 - PowerSeries.C lam * PowerSeries.X -
        PowerSeries.C mu * PowerSeries.X ^ 2 ∧
    h * (1 + PowerSeries.C r * PowerSeries.X +
        PowerSeries.C s * PowerSeries.X ^ 2) =
      PowerSeries.X := by
  have hExpandD : d * (1 + PowerSeries.C r * PowerSeries.X +
        PowerSeries.C s * PowerSeries.X ^ 2) =
      d + PowerSeries.C r * (d * PowerSeries.X) +
        PowerSeries.C s * (d * PowerSeries.X ^ 2) := by ring
  have hdEq : d * (1 + PowerSeries.C r * PowerSeries.X +
        PowerSeries.C s * PowerSeries.X ^ 2) =
      1 - PowerSeries.C lam * PowerSeries.X -
        PowerSeries.C mu * PowerSeries.X ^ 2 := by
    rw [hExpandD, PowerSeries.ext_iff]
    intro N
    have hR := hRec N 0
    have hMid : (if 1 ≤ N ∧ 1 ≤ 0 then L (N - 1) (0 - 1) else 0) = 0 := by
      rw [ite_eq_right (by omega : ¬ (1 ≤ N ∧ 1 ≤ 0))]
    rw [hMid, sub_zero, ite_eq_left rfl] at hR
    rw [map_add, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
      coeff_one_sub lam mu N]
    rw [coeff_mul_X d N, coeff_mul_X_pow_two d N]
    have e1 : (if 1 ≤ N then PowerSeries.coeff (N - 1) d else 0) =
        (if 1 ≤ N then L (N - 1) 0 else 0) := by
      by_cases hN : 1 ≤ N
      · rw [ite_eq_left hN, ite_eq_left hN, hL (N - 1) 0, pow_zero, mul_one]
      · rw [ite_eq_right hN, ite_eq_right hN]
    have e2 : (if 2 ≤ N then PowerSeries.coeff (N - 2) d else 0) =
        (if 2 ≤ N then L (N - 2) 0 else 0) := by
      by_cases hN : 2 ≤ N
      · rw [ite_eq_left hN, ite_eq_left hN, hL (N - 2) 0, pow_zero, mul_one]
      · rw [ite_eq_right hN, ite_eq_right hN]
    rw [e1, e2]
    have hLN : L N 0 = PowerSeries.coeff N d := by
      rw [hL N 0, pow_zero, mul_one]
    rw [hLN] at hR
    linarith [hR]
  refine ⟨hdEq, ?_⟩
  have hCd : PowerSeries.constantCoeff d ≠ 0 := by
    have hEq : PowerSeries.coeff 0 d = PowerSeries.constantCoeff d :=
      congrFun PowerSeries.coeff_zero_eq_constantCoeff d
    rwa [hEq] at hd0
  have hInv : d⁻¹ * d = 1 := PowerSeries.inv_mul_cancel _ hCd
  have hExpandH : d * h ^ (0 + 1) * (1 + PowerSeries.C r * PowerSeries.X +
        PowerSeries.C s * PowerSeries.X ^ 2) =
      d * h ^ (0 + 1) + PowerSeries.C r * ((d * h ^ (0 + 1)) * PowerSeries.X) +
        PowerSeries.C s * ((d * h ^ (0 + 1)) * PowerSeries.X ^ 2) := by ring
  have hKey : d * (h * (1 + PowerSeries.C r * PowerSeries.X +
        PowerSeries.C s * PowerSeries.X ^ 2)) = d * PowerSeries.X := by
    have hPow1 : h ^ (0 + 1) = h := by rw [zero_add, pow_one]
    have hDH : d * h ^ (0 + 1) * (1 + PowerSeries.C r * PowerSeries.X +
          PowerSeries.C s * PowerSeries.X ^ 2) =
        PowerSeries.X * d := by
      rw [hExpandH, PowerSeries.ext_iff]
      intro N
      have hR := hRec N 1
      have hK0 : (if (1 : ℕ) = 0 then
          (if N = 0 then (1 : ℝ) else if N = 1 then -lam
            else if N = 2 then -mu else 0) else 0) = 0 := by
        rw [ite_eq_right (by omega : ¬ (1 : ℕ) = 0)]
      rw [hK0] at hR
      have hMid : (if 1 ≤ N ∧ 1 ≤ 1 then L (N - 1) (1 - 1) else 0) =
          (if 1 ≤ N then L (N - 1) 0 else 0) := by
        by_cases hN : 1 ≤ N
        · rw [ite_eq_left ⟨hN, by omega⟩, ite_eq_left hN]
        · rw [ite_eq_right (by omega : ¬ (1 ≤ N ∧ 1 ≤ 1)),
            ite_eq_right hN]
      rw [hMid] at hR
      rw [map_add, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
      rw [coeff_mul_X (d * h ^ (0 + 1)) N,
        coeff_mul_X_pow_two (d * h ^ (0 + 1)) N]
      have hX : PowerSeries.coeff N (PowerSeries.X * d) =
          (if 1 ≤ N then L (N - 1) 0 else 0) := by
        cases N with
        | zero =>
          rw [PowerSeries.coeff_zero_X_mul]
          rw [ite_eq_right (by omega : ¬ 1 ≤ 0)]
        | succ m =>
          rw [PowerSeries.coeff_succ_X_mul]
          rw [ite_eq_left (by omega : 1 ≤ m + 1)]
          have hm : m + 1 - 1 = m := by omega
          rw [hm, hL m 0, pow_zero, mul_one]
      rw [hX]
      have e1 : (if 1 ≤ N then
          PowerSeries.coeff (N - 1) (d * h ^ (0 + 1)) else 0) =
          (if 1 ≤ N then L (N - 1) 1 else 0) := by
        by_cases hN : 1 ≤ N
        · rw [ite_eq_left hN, ite_eq_left hN, hL (N - 1) 1]
        · rw [ite_eq_right hN, ite_eq_right hN]
      have e2 : (if 2 ≤ N then
          PowerSeries.coeff (N - 2) (d * h ^ (0 + 1)) else 0) =
          (if 2 ≤ N then L (N - 2) 1 else 0) := by
        by_cases hN : 2 ≤ N
        · rw [ite_eq_left hN, ite_eq_left hN, hL (N - 2) 1]
        · rw [ite_eq_right hN, ite_eq_right hN]
      rw [e1, e2]
      have hLN : L N 1 = PowerSeries.coeff N (d * h ^ (0 + 1)) := by
        rw [hL N 1]
      rw [hLN] at hR
      linarith [hR]
    rw [hPow1] at hDH
    have hComm : (PowerSeries.X : PowerSeries ℝ) * d = d * PowerSeries.X := by ring
    rw [hComm] at hDH
    have hAssoc : d * h * (1 + PowerSeries.C r * PowerSeries.X +
        PowerSeries.C s * PowerSeries.X ^ 2) =
        d * (h * (1 + PowerSeries.C r * PowerSeries.X +
          PowerSeries.C s * PowerSeries.X ^ 2)) := by ring
    rw [hAssoc] at hDH
    exact hDH
  have hCancel := congrArg (fun F => d⁻¹ * F) hKey
  rw [← mul_assoc d⁻¹ d _, ← mul_assoc d⁻¹ d _, hInv, one_mul, one_mul] at hCancel
  exact hCancel

/-- The recurrence forces `L 0 0 = 1`. -/
private theorem recurrence_L00 (L : ℕ → ℕ → ℝ)
    (lam mu r s : ℝ)
    (hRec : ∀ N K : ℕ,
      L N K + r * (if 1 ≤ N then L (N - 1) K else 0) -
          (if 1 ≤ N ∧ 1 ≤ K then L (N - 1) (K - 1) else 0) +
          s * (if 2 ≤ N then L (N - 2) K else 0) =
        (if K = 0 then
          if N = 0 then 1 else if N = 1 then -lam else if N = 2 then -mu else 0
        else 0)) :
    L 0 0 = 1 := by
  have hR := hRec 0 0
  rw [ite_eq_right (by omega : ¬ (1 : ℕ) ≤ 0),
    ite_eq_right (by omega : ¬ (1 ≤ (0 : ℕ) ∧ 1 ≤ 0)),
    ite_eq_right (by omega : ¬ (2 : ℕ) ≤ 0)] at hR
  rw [ite_eq_left rfl, ite_eq_left rfl] at hR
  linarith [hR]

/-- The recurrence plus triangularity forces unit diagonal. -/
private theorem recurrence_diag_eq_one (L : ℕ → ℕ → ℝ)
    (hTri : ∀ n k : ℕ, n < k → L n k = 0)
    (lam mu r s : ℝ)
    (hRec : ∀ N K : ℕ,
      L N K + r * (if 1 ≤ N then L (N - 1) K else 0) -
          (if 1 ≤ N ∧ 1 ≤ K then L (N - 1) (K - 1) else 0) +
          s * (if 2 ≤ N then L (N - 2) K else 0) =
        (if K = 0 then
          if N = 0 then 1 else if N = 1 then -lam else if N = 2 then -mu else 0
        else 0)) :
    ∀ n : ℕ, L n n = 1 := by
  have h00 : L 0 0 = 1 := recurrence_L00 L lam mu r s hRec
  intro n
  induction n with
  | zero => exact h00
  | succ m ih =>
    have hR := hRec (m + 1) (m + 1)
    have hK : (if m + 1 = 0 then
        (if m + 1 = 0 then (1 : ℝ) else if m + 1 = 1 then -lam
          else if m + 1 = 2 then -mu else 0) else 0) = 0 := by
      rw [ite_eq_right (by omega : ¬ m + 1 = 0)]
    rw [hK] at hR
    have hUp : L m (m + 1) = 0 := hTri m (m + 1) (by omega)
    have hUp2 : L (m + 1 - 2) (m + 1) = 0 :=
      hTri (m + 1 - 2) (m + 1) (by omega)
    have hMid : (if 1 ≤ m + 1 ∧ 1 ≤ m + 1 then L (m + 1 - 1) (m + 1 - 1)
        else 0) = L m m := by
      rw [ite_eq_left ⟨by omega, by omega⟩]
      have e1 : m + 1 - 1 = m := by omega
      rw [e1]
    have hLo : (if 1 ≤ m + 1 then L (m + 1 - 1) (m + 1) else 0) = 0 := by
      rw [ite_eq_left (by omega : 1 ≤ m + 1)]
      have e1 : m + 1 - 1 = m := by omega
      rw [e1, hUp]
    have hLo2 : (if 2 ≤ m + 1 then L (m + 1 - 2) (m + 1) else 0) = 0 := by
      by_cases h2 : 2 ≤ m + 1
      · rw [ite_eq_left h2, hUp2]
      · rw [ite_eq_right h2]
    rw [hLo, hMid, hLo2] at hR
    rw [ih] at hR
    linarith [hR]

/-- Polynomial with row `n` of `L` as coefficients. -/
private noncomputable def polyOfRow (L : ℕ → ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.monomial k (L n k)

/-- Coefficients of `polyOfRow` recover the row. -/
private theorem polyOfRow_coeff (L : ℕ → ℕ → ℝ)
    (hTri : ∀ n k : ℕ, n < k → L n k = 0) (n j : ℕ) :
    Polynomial.coeff (polyOfRow L n) j = L n j := by
  have hSum : Polynomial.coeff (∑ k ∈ Finset.range (n + 1),
      Polynomial.monomial k (L n k)) j =
      ∑ k ∈ Finset.range (n + 1),
        Polynomial.coeff (Polynomial.monomial k (L n k)) j := by
    rw [← Polynomial.lcoeff_apply, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Polynomial.lcoeff_apply]
  rw [polyOfRow, hSum]
  have hEq : (∑ k ∈ Finset.range (n + 1),
      Polynomial.coeff (Polynomial.monomial k (L n k)) j) =
      ∑ k ∈ Finset.range (n + 1), (if k = j then L n k else 0) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [Polynomial.coeff_monomial]
  rw [hEq, Finset.sum_ite_eq']
  by_cases hj : j ∈ Finset.range (n + 1)
  · rw [ite_eq_left hj]
  · rw [ite_eq_right hj]
    rw [Finset.mem_range] at hj
    have hLT : n < j := by omega
    exact (hTri n j hLT).symm

/-- `polyOfRow` is monic when the diagonal is one. -/
private theorem polyOfRow_monic (L : ℕ → ℕ → ℝ)
    (hTri : ∀ n k : ℕ, n < k → L n k = 0)
    (hDiag : ∀ n : ℕ, L n n = 1) (n : ℕ) :
    (polyOfRow L n).Monic := by
  have hPL : ∀ k : ℕ, Polynomial.coeff (polyOfRow L n) k = L n k :=
    fun k => polyOfRow_coeff L hTri n k
  have hDeg : (polyOfRow L n).natDegree = n := by
    apply le_antisymm
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rw [hPL k]
      exact hTri n k hk
    · by_contra hlt
      push Not at hlt
      have h0 : Polynomial.coeff (polyOfRow L n) n = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt hlt
      rw [hPL n, hDiag n] at h0
      exact one_ne_zero h0
  rw [Polynomial.Monic, Polynomial.leadingCoeff, hDeg, hPL n, hDiag n]

/-- Coefficient of `X * p` at `k` in terms of `p`. -/
private theorem coeff_X_mul_all (p : Polynomial ℝ) (k : ℕ) :
    Polynomial.coeff (Polynomial.X * p) k =
      (if k = 0 then 0 else Polynomial.coeff p (k - 1)) := by
  cases k with
  | zero =>
    rw [ite_eq_left rfl]
    rw [Polynomial.coeff_X_mul_zero]
  | succ m =>
    rw [ite_eq_right (by omega : ¬ m + 1 = 0)]
    rw [Polynomial.coeff_X_mul]
    have hm : m + 1 - 1 = m := by omega
    rw [hm]

/-- Row-zero polynomial is one under the recurrence. -/
private theorem polyOfRow_zero (L : ℕ → ℕ → ℝ)
    (hTri : ∀ n k : ℕ, n < k → L n k = 0)
    (lam mu r s : ℝ)
    (hRec : ∀ N K : ℕ,
      L N K + r * (if 1 ≤ N then L (N - 1) K else 0) -
          (if 1 ≤ N ∧ 1 ≤ K then L (N - 1) (K - 1) else 0) +
          s * (if 2 ≤ N then L (N - 2) K else 0) =
        (if K = 0 then
          if N = 0 then 1 else if N = 1 then -lam else if N = 2 then -mu else 0
        else 0)) :
    polyOfRow L 0 = 1 := by
  have h00 : L 0 0 = 1 := recurrence_L00 L lam mu r s hRec
  rw [Polynomial.ext_iff]
  intro k
  rw [polyOfRow_coeff L hTri 0 k, Polynomial.coeff_one]
  by_cases hk : k = 0
  · rw [ite_eq_left hk, hk]
    exact h00
  · rw [ite_eq_right hk]
    exact hTri 0 k (by omega)

/-- Favard recurrence, coefficient form on `L`. -/
private theorem favard_L_eq (L : ℕ → ℕ → ℝ)
    (P : ℕ → Polynomial ℝ)
    (hPL : ∀ n k : ℕ, Polynomial.coeff (P n) k = L n k)
    (α β : ℕ → ℝ)
    (hrec : ∀ n : ℕ, P (n + 2) = (Polynomial.X - Polynomial.C (α (n + 1))) *
      P (n + 1) - Polynomial.C (β (n + 1)) * P n) :
    ∀ n k : ℕ, L (n + 2) k =
      (if k = 0 then 0 else L (n + 1) (k - 1)) -
        α (n + 1) * L (n + 1) k - β (n + 1) * L n k := by
  intro n k
  have hCoeff := congrArg (fun Q => Polynomial.coeff Q k) (hrec n)
  have hExpand : (Polynomial.X - Polynomial.C (α (n + 1))) * P (n + 1) -
      Polynomial.C (β (n + 1)) * P n =
      Polynomial.X * P (n + 1) - Polynomial.C (α (n + 1)) * P (n + 1) -
        Polynomial.C (β (n + 1)) * P n := by ring
  rw [hExpand, Polynomial.coeff_sub, Polynomial.coeff_sub,
    Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
    coeff_X_mul_all (P (n + 1)) k] at hCoeff
  rw [hPL (n + 2) k, hPL (n + 1) k, hPL n k] at hCoeff
  have hX : (if k = 0 then (0 : ℝ) else Polynomial.coeff (P (n + 1)) (k - 1)) =
      (if k = 0 then 0 else L (n + 1) (k - 1)) := by
    by_cases hk : k = 0
    · rw [ite_eq_left hk, ite_eq_left hk]
    · rw [ite_eq_right hk, ite_eq_right hk, hPL (n + 1) (k - 1)]
  rw [hX] at hCoeff
  linarith [hCoeff]

/-- Row-one polynomial under the recurrence. -/
private theorem polyOfRow_one (L : ℕ → ℕ → ℝ)
    (hTri : ∀ n k : ℕ, n < k → L n k = 0)
    (lam mu r s : ℝ)
    (hRec : ∀ N K : ℕ,
      L N K + r * (if 1 ≤ N then L (N - 1) K else 0) -
          (if 1 ≤ N ∧ 1 ≤ K then L (N - 1) (K - 1) else 0) +
          s * (if 2 ≤ N then L (N - 2) K else 0) =
        (if K = 0 then
          if N = 0 then 1 else if N = 1 then -lam else if N = 2 then -mu else 0
        else 0)) :
    polyOfRow L 1 = Polynomial.X - Polynomial.C (r + lam) := by
  have h00 : L 0 0 = 1 := recurrence_L00 L lam mu r s hRec
  have hDiag := recurrence_diag_eq_one L hTri lam mu r s hRec
  have h10 : L 1 0 = -(r + lam) := by
    have hR := hRec 1 0
    have hMid : (if 1 ≤ 1 ∧ 1 ≤ 0 then L (1 - 1) (0 - 1) else 0) = 0 := by
      rw [ite_eq_right (by omega : ¬ (1 ≤ (1 : ℕ) ∧ 1 ≤ 0))]
    have hLo : (if 1 ≤ (1 : ℕ) then L (1 - 1) 0 else 0) = L 0 0 := by
      rw [ite_eq_left (by omega : 1 ≤ 1)]
    have hLo2 : (if 2 ≤ (1 : ℕ) then L (1 - 2) 0 else 0) = 0 := by
      rw [ite_eq_right (by omega : ¬ 2 ≤ (1 : ℕ))]
    have hK : (if (0 : ℕ) = 0 then
        (if (1 : ℕ) = 0 then (1 : ℝ) else if 1 = 1 then -lam
          else if 1 = 2 then -mu else 0) else 0) = -lam := by
      rw [ite_eq_left rfl, ite_eq_right (by omega : ¬ (1 : ℕ) = 0),
        ite_eq_left rfl]
    rw [hMid, hLo, hLo2, hK, h00] at hR
    linarith [hR]
  rw [Polynomial.ext_iff]
  intro k
  rw [polyOfRow_coeff L hTri 1 k, Polynomial.coeff_sub, Polynomial.coeff_X,
    Polynomial.coeff_C]
  by_cases hk0 : k = 0
  · rw [ite_eq_left hk0]
    have hk1 : ¬ (1 : ℕ) = k := by omega
    rw [ite_eq_right hk1]
    rw [hk0, h10]
    ring
  · rw [ite_eq_right hk0]
    by_cases hk1 : k = 1
    · have h1k : (1 : ℕ) = k := by omega
      rw [ite_eq_left h1k]
      rw [hk1, hDiag 1]
      ring
    · have h1k : ¬ (1 : ℕ) = k := by omega
      rw [ite_eq_right h1k, sub_self]
      exact hTri 1 k (by omega)

/-- Three-term recurrence for rows under the coefficient recurrence. -/
private theorem polyOfRow_recurrence (L : ℕ → ℕ → ℝ)
    (hTri : ∀ n k : ℕ, n < k → L n k = 0)
    (lam mu r s : ℝ)
    (hRec : ∀ N K : ℕ,
      L N K + r * (if 1 ≤ N then L (N - 1) K else 0) -
          (if 1 ≤ N ∧ 1 ≤ K then L (N - 1) (K - 1) else 0) +
          s * (if 2 ≤ N then L (N - 2) K else 0) =
        (if K = 0 then
          if N = 0 then 1 else if N = 1 then -lam else if N = 2 then -mu else 0
        else 0))
    (α β : ℕ → ℝ)
    (hαS : ∀ n : ℕ, α (n + 1) = r)
    (hβ1 : β 1 = s + mu) (hβS : ∀ n : ℕ, β (n + 2) = s) :
    ∀ n : ℕ, polyOfRow L (n + 2) = (Polynomial.X - Polynomial.C (α (n + 1))) *
      polyOfRow L (n + 1) - Polynomial.C (β (n + 1)) * polyOfRow L n := by
  have h00 : L 0 0 = 1 := recurrence_L00 L lam mu r s hRec
  intro n
  cases n with
  | zero =>
    have hα1 : α (0 + 1) = r := hαS 0
    have hβ1' : β (0 + 1) = s + mu := by
      have h01 : (0 : ℕ) + 1 = 1 := by omega
      rw [h01, hβ1]
    rw [hα1, hβ1']
    rw [Polynomial.ext_iff]
    intro k
    have hR := hRec 2 k
    have hLo : (if 1 ≤ (2 : ℕ) then L (2 - 1) k else 0) = L 1 k := by
      rw [ite_eq_left (by omega : 1 ≤ 2)]
    have hLo2 : (if 2 ≤ (2 : ℕ) then L (2 - 2) k else 0) = L 0 k := by
      rw [ite_eq_left (by omega : 2 ≤ 2)]
    have hMid : (if 1 ≤ (2 : ℕ) ∧ 1 ≤ k then L (2 - 1) (k - 1) else 0) =
        (if 1 ≤ k then L 1 (k - 1) else 0) := by
      by_cases hk : 1 ≤ k
      · rw [ite_eq_left ⟨by omega, hk⟩, ite_eq_left hk]
      · rw [ite_eq_right (by omega : ¬ (1 ≤ 2 ∧ 1 ≤ k)), ite_eq_right hk]
    rw [hLo, hLo2, hMid] at hR
    have hCoeff : Polynomial.coeff
        ((Polynomial.X - Polynomial.C r) * polyOfRow L (0 + 1) -
          Polynomial.C (s + mu) * polyOfRow L 0) k =
        (if k = 0 then 0 else L 1 (k - 1)) - r * L 1 k - (s + mu) * L 0 k := by
      have hExpand : (Polynomial.X - Polynomial.C r) * polyOfRow L (0 + 1) -
          Polynomial.C (s + mu) * polyOfRow L 0 =
          Polynomial.X * polyOfRow L (0 + 1) -
            Polynomial.C r * polyOfRow L (0 + 1) -
            Polynomial.C (s + mu) * polyOfRow L 0 := by ring
      rw [hExpand, Polynomial.coeff_sub, Polynomial.coeff_sub,
        Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
        coeff_X_mul_all (polyOfRow L (0 + 1)) k,
        polyOfRow_coeff L hTri 1 k, polyOfRow_coeff L hTri 0 k]
      have hX : (if k = 0 then (0 : ℝ)
          else Polynomial.coeff (polyOfRow L (0 + 1)) (k - 1)) =
          (if k = 0 then 0 else L 1 (k - 1)) := by
        by_cases hk : k = 0
        · rw [ite_eq_left hk, ite_eq_left hk]
        · rw [ite_eq_right hk, ite_eq_right hk,
            polyOfRow_coeff L hTri 1 (k - 1)]
      rw [hX]
    rw [polyOfRow_coeff L hTri 2 k, hCoeff]
    by_cases hk0 : k = 0
    · rw [ite_eq_left hk0]
      rw [ite_eq_right (by omega : ¬ 1 ≤ k)] at hR
      have hK : (if k = 0 then
          (if (2 : ℕ) = 0 then (1 : ℝ) else if 2 = 1 then -lam
            else if 2 = 2 then -mu else 0) else 0) = -mu := by
        rw [ite_eq_left hk0, ite_eq_right (by omega : ¬ (2 : ℕ) = 0),
          ite_eq_right (by omega : ¬ (2 : ℕ) = 1), ite_eq_left rfl]
      rw [hK] at hR
      rw [hk0, h00] at hR ⊢
      linarith [hR]
    · rw [ite_eq_right hk0]
      have hk1 : 1 ≤ k := by omega
      rw [ite_eq_left hk1] at hR
      have hK : (if k = 0 then
          (if (2 : ℕ) = 0 then (1 : ℝ) else if 2 = 1 then -lam
            else if 2 = 2 then -mu else 0) else 0) = 0 := by
        rw [ite_eq_right hk0]
      rw [hK] at hR
      have hL0 : L 0 k = 0 := hTri 0 k (by omega)
      rw [hL0] at hR ⊢
      linarith [hR]
  | succ m =>
    have hα : α (m + 1 + 1) = r := hαS (m + 1)
    have hβ : β (m + 1 + 1) = s := by
      cases m with
      | zero => exact hβS 0
      | succ t =>
        have hEq : t + 1 + 1 + 1 = (t + 1) + 2 := by omega
        rw [hEq]
        exact hβS (t + 1)
    rw [hα, hβ]
    rw [Polynomial.ext_iff]
    intro k
    have hR := hRec (m + 1 + 2) k
    have hN1 : (1 : ℕ) ≤ m + 1 + 2 := by omega
    have hN2 : (2 : ℕ) ≤ m + 1 + 2 := by omega
    have hLo : (if 1 ≤ m + 1 + 2 then L (m + 1 + 2 - 1) k else 0) =
        L (m + 1 + 1) k := by
      rw [ite_eq_left hN1]
      have e1 : m + 1 + 2 - 1 = m + 1 + 1 := by omega
      rw [e1]
    have hLo2 : (if 2 ≤ m + 1 + 2 then L (m + 1 + 2 - 2) k else 0) =
        L (m + 1) k := by
      rw [ite_eq_left hN2]
      have e2 : m + 1 + 2 - 2 = m + 1 := by omega
      rw [e2]
    have hMid : (if 1 ≤ m + 1 + 2 ∧ 1 ≤ k then L (m + 1 + 2 - 1) (k - 1)
        else 0) = (if 1 ≤ k then L (m + 1 + 1) (k - 1) else 0) := by
      by_cases hk : 1 ≤ k
      · rw [ite_eq_left ⟨hN1, hk⟩, ite_eq_left hk]
        have e1 : m + 1 + 2 - 1 = m + 1 + 1 := by omega
        rw [e1]
      · rw [ite_eq_right (by omega : ¬ (1 ≤ m + 1 + 2 ∧ 1 ≤ k)),
          ite_eq_right hk]
    rw [hLo, hLo2, hMid] at hR
    have hK : (if k = 0 then
        (if m + 1 + 2 = 0 then (1 : ℝ) else if m + 1 + 2 = 1 then -lam
          else if m + 1 + 2 = 2 then -mu else 0) else 0) = 0 := by
      by_cases hk : k = 0
      · rw [ite_eq_left hk, ite_eq_right (by omega : ¬ m + 1 + 2 = 0),
          ite_eq_right (by omega : ¬ m + 1 + 2 = 1),
          ite_eq_right (by omega : ¬ m + 1 + 2 = 2)]
      · rw [ite_eq_right hk]
    rw [hK] at hR
    have hCoeff : Polynomial.coeff
        ((Polynomial.X - Polynomial.C r) * polyOfRow L (m + 1 + 1) -
          Polynomial.C s * polyOfRow L (m + 1)) k =
        (if k = 0 then 0 else L (m + 1 + 1) (k - 1)) - r * L (m + 1 + 1) k -
          s * L (m + 1) k := by
      have hExpand : (Polynomial.X - Polynomial.C r) * polyOfRow L (m + 1 + 1) -
          Polynomial.C s * polyOfRow L (m + 1) =
          Polynomial.X * polyOfRow L (m + 1 + 1) -
            Polynomial.C r * polyOfRow L (m + 1 + 1) -
            Polynomial.C s * polyOfRow L (m + 1) := by ring
      rw [hExpand, Polynomial.coeff_sub, Polynomial.coeff_sub,
        Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
        coeff_X_mul_all (polyOfRow L (m + 1 + 1)) k,
        polyOfRow_coeff L hTri (m + 1 + 1) k,
        polyOfRow_coeff L hTri (m + 1) k]
      have hX : (if k = 0 then (0 : ℝ)
          else Polynomial.coeff (polyOfRow L (m + 1 + 1)) (k - 1)) =
          (if k = 0 then 0 else L (m + 1 + 1) (k - 1)) := by
        by_cases hk : k = 0
        · rw [ite_eq_left hk, ite_eq_left hk]
        · rw [ite_eq_right hk, ite_eq_right hk,
            polyOfRow_coeff L hTri (m + 1 + 1) (k - 1)]
      rw [hX]
    rw [polyOfRow_coeff L hTri (m + 1 + 2) k, hCoeff]
    by_cases hk0 : k = 0
    · rw [ite_eq_left hk0]
      rw [ite_eq_right (by omega : ¬ 1 ≤ k)] at hR
      linarith [hR]
    · rw [ite_eq_right hk0]
      rw [ite_eq_left (by omega : 1 ≤ k)] at hR
      linarith [hR]

/-- Coefficient recurrence implies monic orthogonality. -/
private theorem recurrence_to_orthogonal (d h : PowerSeries ℝ) (L : ℕ → ℕ → ℝ)
    (h0 : PowerSeries.coeff 0 h = 0)
    (hL : ∀ n k : ℕ, L n k = PowerSeries.coeff n (d * h ^ k))
    (lam mu r s : ℝ) (hs : s ≠ 0) (hsm : s + mu ≠ 0)
    (hRec : ∀ N K : ℕ,
      L N K + r * (if 1 ≤ N then L (N - 1) K else 0) -
          (if 1 ≤ N ∧ 1 ≤ K then L (N - 1) (K - 1) else 0) +
          s * (if 2 ≤ N then L (N - 2) K else 0) =
        (if K = 0 then
          if N = 0 then 1 else if N = 1 then -lam else if N = 2 then -mu else 0
        else 0)) :
    ∃ P : ℕ → Polynomial ℝ,
      (∀ n k : ℕ, Polynomial.coeff (P n) k = L n k) ∧
      (∀ n : ℕ, (P n).Monic) ∧ Polynomial.IsFormallyOrthogonal P := by
  have hTri : ∀ n k : ℕ, n < k → L n k = 0 := by
    intro n k hk
    have hk' : n < k := hk
    exact riordan_L_triangular d h L h0 hL n k hk'
  have hDiag : ∀ n : ℕ, L n n = 1 :=
    recurrence_diag_eq_one L hTri lam mu r s hRec
  refine ⟨polyOfRow L, fun n k => polyOfRow_coeff L hTri n k,
    fun n => polyOfRow_monic L hTri hDiag n, ?_⟩
  have hmonic : ∀ n : ℕ, (polyOfRow L n).Monic :=
    fun n => polyOfRow_monic L hTri hDiag n
  rw [favard_iff (polyOfRow L) hmonic]
  set α : ℕ → ℝ := fun m => match m with | 0 => r + lam | _ + 1 => r with hα
  set β : ℕ → ℝ := fun m => match m with
    | 0 => 0 | 1 => s + mu | _ + 2 => s with hβ
  have hα0 : α 0 = r + lam := rfl
  have hαS : ∀ n : ℕ, α (n + 1) = r := fun n => rfl
  have hβ1 : β 1 = s + mu := rfl
  have hβS : ∀ n : ℕ, β (n + 2) = s := fun n => by
    cases n with
    | zero => rfl
    | succ t =>
      have hEq : t + 1 + 2 = (t + 1) + 2 := by omega
      rw [hEq]
  have hβ : ∀ n : ℕ, β (n + 1) ≠ 0 := by
    intro n
    cases n with
    | zero =>
      have h01 : (0 : ℕ) + 1 = 1 := by omega
      rw [h01, hβ1]
      exact hsm
    | succ t =>
      have hEq : t + 1 + 1 = t + 2 := by omega
      rw [hEq]
      cases t with
      | zero => rw [hβS 0]; exact hs
      | succ u =>
        have hEq2 : u + 1 + 2 = (u + 1) + 2 := by omega
        rw [hEq2]
        rw [hβS (u + 1)]
        exact hs
  have hp0 : polyOfRow L 0 = 1 := polyOfRow_zero L hTri lam mu r s hRec
  have hp1 : polyOfRow L 1 = Polynomial.X - Polynomial.C (α 0) := by
    rw [hα0]
    exact polyOfRow_one L hTri lam mu r s hRec
  have hrec : ∀ n : ℕ, polyOfRow L (n + 2) =
      (Polynomial.X - Polynomial.C (α (n + 1))) * polyOfRow L (n + 1) -
        Polynomial.C (β (n + 1)) * polyOfRow L n :=
    polyOfRow_recurrence L hTri lam mu r s hRec α β hαS hβ1 hβS
  exact ⟨α, β, hβ, hp0, hp1, hrec⟩

/-- Orthogonality plus monicity forces unit diagonal on `L`. -/
private theorem orth_diag_eq_one (L : ℕ → ℕ → ℝ)
    (P : ℕ → Polynomial ℝ)
    (hPL : ∀ n k : ℕ, Polynomial.coeff (P n) k = L n k)
    (hmonic : ∀ n : ℕ, (P n).Monic)
    (horth : Polynomial.IsFormallyOrthogonal P) :
    ∀ n : ℕ, L n n = 1 := by
  obtain ⟨Lfunc, hdeg, _, _⟩ := horth
  intro n
  rw [← hPL n n]
  exact monic_coeff_eq_one (P n) n (hmonic n) (hdeg n)

/-- Unit diagonal forces `d 0 = 1` and `h = X * u` with `u 0 = 1`. -/
private theorem riordan_unit_factors (d h : PowerSeries ℝ) (L : ℕ → ℕ → ℝ)
    (h0 : PowerSeries.coeff 0 h = 0)
    (hL : ∀ n k : ℕ, L n k = PowerSeries.coeff n (d * h ^ k))
    (hDiag : ∀ n : ℕ, L n n = 1) :
    PowerSeries.coeff 0 d = 1 ∧
    ∃ u : PowerSeries ℝ, h = PowerSeries.X * u ∧ PowerSeries.coeff 0 u = 1 := by
  have hd0 : PowerSeries.coeff 0 d = 1 := by
    have h00 := hDiag 0
    rw [hL 0 0, pow_zero, mul_one] at h00
    exact h00
  refine ⟨hd0, ?_⟩
  have hX : (PowerSeries.X : PowerSeries ℝ) ∣ h := by
    rw [PowerSeries.X_dvd_iff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact h0
  obtain ⟨u, hu⟩ := hX
  refine ⟨u, hu, ?_⟩
  have h11 := hDiag 1
  rw [hL 1 1] at h11
  have hComm : d * h = PowerSeries.X * (d * u) := by
    rw [hu]; ring
  rw [pow_one, hComm, PowerSeries.coeff_succ_X_mul] at h11
  have hCu : PowerSeries.constantCoeff (d * u) =
      PowerSeries.constantCoeff d * PowerSeries.constantCoeff u := map_mul _ _ _
  have hCd : PowerSeries.constantCoeff d = 1 := by
    have hEq : PowerSeries.coeff 0 d = PowerSeries.constantCoeff d :=
      congrFun PowerSeries.coeff_zero_eq_constantCoeff d
    rw [hd0] at hEq
    exact hEq.symm
  have hCdu : PowerSeries.constantCoeff (d * u) = 1 := by
    have hEq : PowerSeries.coeff 0 (d * u) = PowerSeries.constantCoeff (d * u) :=
      congrFun PowerSeries.coeff_zero_eq_constantCoeff (d * u)
    rw [h11] at hEq
    exact hEq.symm
  rw [hCu, hCd, one_mul] at hCdu
  have hEqU : PowerSeries.coeff 0 u = PowerSeries.constantCoeff u :=
    congrFun PowerSeries.coeff_zero_eq_constantCoeff u
  rw [hCdu] at hEqU
  exact hEqU

/-- Subdiagonal entries via the unit part. -/
private theorem riordan_subdiag (d h u : PowerSeries ℝ) (L : ℕ → ℕ → ℝ)
    (hu : h = PowerSeries.X * u)
    (hL : ∀ n k : ℕ, L n k = PowerSeries.coeff n (d * h ^ k)) (n t : ℕ) :
    L (n + t) n = PowerSeries.coeff t (d * u ^ n) := by
  have hPow : h ^ n = PowerSeries.X ^ n * u ^ n := by
    rw [hu, mul_pow]
  have hDH : d * h ^ n = PowerSeries.X ^ n * (d * u ^ n) := by
    rw [hPow]; ring
  rw [hL (n + t) n, hDH]
  have hAdd : n + t = t + n := by omega
  rw [hAdd, PowerSeries.coeff_X_pow_mul]

/-- First Jacobi parameter is constant on `n ≥ 1`. -/
private theorem alpha_const (d h u : PowerSeries ℝ) (L : ℕ → ℕ → ℝ)
    (hL : ∀ n k : ℕ, L n k = PowerSeries.coeff n (d * h ^ k))
    (hu : h = PowerSeries.X * u)
    (hd0 : PowerSeries.coeff 0 d = 1) (hu0 : PowerSeries.coeff 0 u = 1)
    (hTri : ∀ n k : ℕ, n < k → L n k = 0)
    (hDiag : ∀ n : ℕ, L n n = 1)
    (α β : ℕ → ℝ) (v : PowerSeries ℝ)
    (hvEq : (1 : PowerSeries ℝ) - u = PowerSeries.X * v)
    (hFav : ∀ n k : ℕ, L (n + 2) k =
      (if k = 0 then 0 else L (n + 1) (k - 1)) -
        α (n + 1) * L (n + 1) k - β (n + 1) * L n k) :
    ∀ n : ℕ, α (n + 1) = PowerSeries.coeff 0 v := by
  intro n
  have hFavN := hFav n (n + 1)
  have hk0 : ¬ (n + 1 : ℕ) = 0 := by omega
  rw [ite_eq_right hk0] at hFavN
  have hD1 : L (n + 1) (n + 1) = 1 := hDiag (n + 1)
  have hT0 : L n (n + 1) = 0 := hTri n (n + 1) (by omega)
  rw [hD1, hT0] at hFavN
  have hSub1 : L (n + 1) n = PowerSeries.coeff 1 (d * u ^ n) := by
    have hEq : n + 1 = n + 1 := rfl
    have hS := riordan_subdiag d h u L hu hL n 1
    rwa [hEq] at hS
  have hSub2 : L (n + 2) (n + 1) = PowerSeries.coeff 1 (d * u ^ (n + 1)) := by
    have hEq : n + 2 = (n + 1) + 1 := by omega
    rw [hEq]
    exact riordan_subdiag d h u L hu hL (n + 1) 1
  have hKm1 : n + 1 - 1 = n := by omega
  rw [hKm1] at hFavN
  have hα : α (n + 1) = L (n + 1) n - L (n + 2) (n + 1) := by
    linarith [hFavN]
  rw [hα, hSub1, hSub2]
  have hDiff : PowerSeries.coeff 1 (d * u ^ n) -
      PowerSeries.coeff 1 (d * u ^ (n + 1)) =
      PowerSeries.coeff 1 (d * u ^ n * (1 - u)) := by
    have hSub : PowerSeries.coeff 1 (d * u ^ n) -
        PowerSeries.coeff 1 (d * u ^ (n + 1)) =
        PowerSeries.coeff 1 (d * u ^ n - d * u ^ (n + 1)) := by
      rw [map_sub]
    rw [hSub]
    congr 1
    have hPow : u ^ (n + 1) = u ^ n * u := by rw [pow_succ]
    rw [hPow]; ring
  rw [hDiff, hvEq]
  have hComm : d * u ^ n * (PowerSeries.X * v) =
      PowerSeries.X * (d * u ^ n * v) := by ring
  rw [hComm]
  have h1 : (1 : ℕ) = 0 + 1 := by omega
  rw [h1, PowerSeries.coeff_succ_X_mul]
  have hCd : PowerSeries.constantCoeff d = 1 := by
    have hEq : PowerSeries.coeff 0 d = PowerSeries.constantCoeff d :=
      congrFun PowerSeries.coeff_zero_eq_constantCoeff d
    rw [hd0] at hEq
    exact hEq.symm
  have hCu : PowerSeries.constantCoeff u = 1 := by
    have hEq : PowerSeries.coeff 0 u = PowerSeries.constantCoeff u :=
      congrFun PowerSeries.coeff_zero_eq_constantCoeff u
    rw [hu0] at hEq
    exact hEq.symm
  have hC : PowerSeries.constantCoeff (d * u ^ n * v) =
      PowerSeries.constantCoeff v := by
    rw [map_mul, map_mul, map_pow, hCd, hCu, one_pow, one_mul, one_mul]
  have hEq1 : PowerSeries.coeff 0 (d * u ^ n * v) =
      PowerSeries.constantCoeff (d * u ^ n * v) :=
    congrFun PowerSeries.coeff_zero_eq_constantCoeff (d * u ^ n * v)
  have hEqV : PowerSeries.coeff 0 v = PowerSeries.constantCoeff v :=
    congrFun PowerSeries.coeff_zero_eq_constantCoeff v
  rw [hEq1, hC, ← hEqV]

/-- Second Jacobi parameter is constant on `n ≥ 2`. -/
private theorem beta_const (d h u : PowerSeries ℝ) (L : ℕ → ℕ → ℝ)
    (hL : ∀ n k : ℕ, L n k = PowerSeries.coeff n (d * h ^ k))
    (hu : h = PowerSeries.X * u)
    (hd0 : PowerSeries.coeff 0 d = 1) (hu0 : PowerSeries.coeff 0 u = 1)
    (hDiag : ∀ n : ℕ, L n n = 1)
    (α β : ℕ → ℝ) (r : ℝ) (v : PowerSeries ℝ)
    (hvEq : (1 : PowerSeries ℝ) - u = PowerSeries.X * v)
    (hr : r = PowerSeries.coeff 0 v)
    (hα : ∀ n : ℕ, α (n + 1) = r)
    (hFav : ∀ n k : ℕ, L (n + 2) k =
      (if k = 0 then 0 else L (n + 1) (k - 1)) -
        α (n + 1) * L (n + 1) k - β (n + 1) * L n k) :
    ∃ c : ℝ, ∀ n : ℕ, β (n + 2) = c := by
  have hvr : PowerSeries.coeff 0 (v - PowerSeries.C r * u) = 0 := by
    rw [map_sub, PowerSeries.coeff_C_mul, hu0, mul_one, hr, sub_self]
  have hXdv : (PowerSeries.X : PowerSeries ℝ) ∣ (v - PowerSeries.C r * u) := by
    rw [PowerSeries.X_dvd_iff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hvr
  obtain ⟨w, hw⟩ := hXdv
  refine ⟨PowerSeries.coeff 0 w, fun n => ?_⟩
  have hFavN := hFav (n + 1) (n + 1)
  have hk0 : ¬ (n + 1 : ℕ) = 0 := by omega
  rw [ite_eq_right hk0] at hFavN
  have hD1 : L (n + 1) (n + 1) = 1 := hDiag (n + 1)
  rw [hD1, hα (n + 1)] at hFavN
  have hKm1 : n + 1 - 1 = n := by omega
  rw [hKm1] at hFavN
  have hS1 : L (n + 1 + 2) (n + 1) = PowerSeries.coeff 2 (d * u ^ (n + 1)) := by
    have hEq : n + 1 + 2 = (n + 1) + 2 := by omega
    rw [hEq]
    exact riordan_subdiag d h u L hu hL (n + 1) 2
  have hS2 : L (n + 1 + 1) n = PowerSeries.coeff 2 (d * u ^ n) := by
    have hEq : n + 1 + 1 = n + 2 := by omega
    rw [hEq]
    have hEq2 : n + 2 = n + 2 := rfl
    have hS := riordan_subdiag d h u L hu hL n 2
    rwa [hEq2] at hS
  have hS3 : L (n + 1 + 1) (n + 1) = PowerSeries.coeff 1 (d * u ^ (n + 1)) := by
    have hEq : n + 1 + 1 = (n + 1) + 1 := by omega
    rw [hEq]
    exact riordan_subdiag d h u L hu hL (n + 1) 1
  have hβ : β (n + 1 + 1) =
      L (n + 1 + 1) n - r * L (n + 1 + 1) (n + 1) - L (n + 1 + 2) (n + 1) := by
    linarith [hFavN]
  have hN2 : n + 1 + 1 = n + 2 := by omega
  rw [hN2] at hβ
  rw [hβ, hS1, hS2, hS3]
  have hPow : u ^ (n + 1) = u ^ n * u := by rw [pow_succ]
  have hStep1 : PowerSeries.coeff 2 (d * u ^ n) -
      PowerSeries.coeff 2 (d * u ^ (n + 1)) =
      PowerSeries.coeff 1 (d * u ^ n * v) := by
    have hSub : PowerSeries.coeff 2 (d * u ^ n) -
        PowerSeries.coeff 2 (d * u ^ (n + 1)) =
        PowerSeries.coeff 2 (d * u ^ n - d * u ^ (n + 1)) := by
      rw [map_sub]
    rw [hSub]
    have hFac : d * u ^ n - d * u ^ (n + 1) =
        PowerSeries.X * (d * u ^ n * v) := by
      rw [hPow]
      linear_combination (d * u ^ n) * hvEq
    rw [hFac]
    have h2 : (2 : ℕ) = 1 + 1 := by omega
    rw [h2, PowerSeries.coeff_succ_X_mul]
  have hStep2 : PowerSeries.coeff 2 (d * u ^ n) - r * PowerSeries.coeff 1 (d * u ^ (n + 1)) -
      PowerSeries.coeff 2 (d * u ^ (n + 1)) =
      PowerSeries.coeff 0 w := by
    have hCr : r * PowerSeries.coeff 1 (d * u ^ (n + 1)) =
        PowerSeries.coeff 1 (PowerSeries.C r * (d * u ^ (n + 1))) := by
      rw [PowerSeries.coeff_C_mul]
    have hLin : PowerSeries.coeff 1 (d * u ^ n * v) -
        PowerSeries.coeff 1 (PowerSeries.C r * (d * u ^ (n + 1))) =
        PowerSeries.coeff 1 (d * u ^ n * (v - PowerSeries.C r * u)) := by
      have hSub : PowerSeries.coeff 1 (d * u ^ n * v) -
          PowerSeries.coeff 1 (PowerSeries.C r * (d * u ^ (n + 1))) =
          PowerSeries.coeff 1 (d * u ^ n * v - PowerSeries.C r * (d * u ^ (n + 1))) := by
        rw [map_sub]
      rw [hSub]
      congr 1
      rw [hPow]; ring
    have hCombine : PowerSeries.coeff 2 (d * u ^ n) - r * PowerSeries.coeff 1 (d * u ^ (n + 1)) -
        PowerSeries.coeff 2 (d * u ^ (n + 1)) =
        PowerSeries.coeff 1 (d * u ^ n * v) -
          PowerSeries.coeff 1 (PowerSeries.C r * (d * u ^ (n + 1))) := by
      rw [hCr]
      linarith [hStep1]
    rw [hCombine, hLin, hw]
    have hComm : d * u ^ n * (PowerSeries.X * w) =
        PowerSeries.X * (d * u ^ n * w) := by ring
    rw [hComm]
    have h1 : (1 : ℕ) = 0 + 1 := by omega
    rw [h1, PowerSeries.coeff_succ_X_mul]
    have hCd : PowerSeries.constantCoeff d = 1 := by
      have hEq : PowerSeries.coeff 0 d = PowerSeries.constantCoeff d :=
        congrFun PowerSeries.coeff_zero_eq_constantCoeff d
      rw [hd0] at hEq
      exact hEq.symm
    have hCu : PowerSeries.constantCoeff u = 1 := by
      have hEq : PowerSeries.coeff 0 u = PowerSeries.constantCoeff u :=
        congrFun PowerSeries.coeff_zero_eq_constantCoeff u
      rw [hu0] at hEq
      exact hEq.symm
    have hC : PowerSeries.constantCoeff (d * u ^ n * w) =
        PowerSeries.constantCoeff w := by
      rw [map_mul, map_mul, map_pow, hCd, hCu, one_pow, one_mul, one_mul]
    have hEq1 : PowerSeries.coeff 0 (d * u ^ n * w) =
        PowerSeries.constantCoeff (d * u ^ n * w) :=
      congrFun PowerSeries.coeff_zero_eq_constantCoeff (d * u ^ n * w)
    have hEqW : PowerSeries.coeff 0 w = PowerSeries.constantCoeff w :=
      congrFun PowerSeries.coeff_zero_eq_constantCoeff w
    rw [hEq1, hC, ← hEqW]
  exact hStep2

/-- Monic orthogonality implies the coefficient recurrence. -/
private theorem orthogonal_to_recurrence (d h : PowerSeries ℝ) (L : ℕ → ℕ → ℝ)
    (h0 : PowerSeries.coeff 0 h = 0)
    (hL : ∀ n k : ℕ, L n k = PowerSeries.coeff n (d * h ^ k))
    (P : ℕ → Polynomial ℝ)
    (hPL : ∀ n k : ℕ, Polynomial.coeff (P n) k = L n k)
    (hmonic : ∀ n : ℕ, (P n).Monic)
    (horth : Polynomial.IsFormallyOrthogonal P) :
    ∃ lam mu r s : ℝ, s ≠ 0 ∧ s + mu ≠ 0 ∧
      ∀ N K : ℕ,
        L N K + r * (if 1 ≤ N then L (N - 1) K else 0) -
            (if 1 ≤ N ∧ 1 ≤ K then L (N - 1) (K - 1) else 0) +
            s * (if 2 ≤ N then L (N - 2) K else 0) =
          (if K = 0 then
            if N = 0 then 1 else if N = 1 then -lam else if N = 2 then -mu else 0
          else 0) := by
  obtain ⟨α, β, hβne, hp0, hp1, hrec⟩ := (favard_iff P hmonic).mp horth
  have hDiag : ∀ n : ℕ, L n n = 1 := orth_diag_eq_one L P hPL hmonic horth
  have hTri : ∀ n k : ℕ, n < k → L n k = 0 :=
    fun n k hk => riordan_L_triangular d h L h0 hL n k hk
  have hFav : ∀ n k : ℕ, L (n + 2) k =
      (if k = 0 then 0 else L (n + 1) (k - 1)) -
        α (n + 1) * L (n + 1) k - β (n + 1) * L n k :=
    favard_L_eq L P hPL α β hrec
  obtain ⟨hd0, u, hu, hu0⟩ := riordan_unit_factors d h L h0 hL hDiag
  have h1u : PowerSeries.coeff 0 (1 - u) = 0 := by
    rw [map_sub, PowerSeries.coeff_one, hu0, ite_eq_left rfl, sub_self]
  have hXdv : (PowerSeries.X : PowerSeries ℝ) ∣ (1 - u) := by
    rw [PowerSeries.X_dvd_iff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact h1u
  obtain ⟨v, hv⟩ := hXdv
  have hα : ∀ n : ℕ, α (n + 1) = PowerSeries.coeff 0 v :=
    alpha_const d h u L hL hu hd0 hu0 hTri hDiag α β v hv hFav
  set r : ℝ := PowerSeries.coeff 0 v with hr
  have hrα : ∀ n : ℕ, α (n + 1) = r := fun n => hα n
  obtain ⟨s, hsβ⟩ := beta_const d h u L hL hu hd0 hu0 hDiag α β r v hv rfl hrα hFav
  have hs : s ≠ 0 := by
    have h2 := hsβ 0
    have hβ2 : β (0 + 2) ≠ 0 := by
      have hEq : (0 : ℕ) + 2 = 1 + 1 := by omega
      rw [hEq]
      exact hβne 1
    rwa [h2] at hβ2
  have hβ1ne : β 1 ≠ 0 := by
    have hEq : (1 : ℕ) = 0 + 1 := by omega
    rw [hEq]
    exact hβne 0
  set lam : ℝ := α 0 - r with hlam
  set mu : ℝ := β 1 - s with hmu
  have hsm : s + mu ≠ 0 := by
    rw [hmu]
    have hAdd : s + (β 1 - s) = β 1 := by ring
    rw [hAdd]
    exact hβ1ne
  have hlam : α 0 = r + lam := by rw [hlam]; ring
  have hmu : β 1 = s + mu := by rw [hmu]; ring
  refine ⟨lam, mu, r, s, hs, hsm, fun N K => ?_⟩
  cases N with
  | zero =>
    cases K with
    | zero =>
      have hMid : (if 1 ≤ (0 : ℕ) ∧ 1 ≤ 0 then L (0 - 1) (0 - 1) else 0) = 0 := by
        rw [ite_eq_right (by omega : ¬ (1 ≤ (0 : ℕ) ∧ 1 ≤ 0))]
      have hLo : (if 1 ≤ (0 : ℕ) then L (0 - 1) 0 else 0) = 0 := by
        rw [ite_eq_right (by omega : ¬ 1 ≤ (0 : ℕ))]
      have hLo2 : (if 2 ≤ (0 : ℕ) then L (0 - 2) 0 else 0) = 0 := by
        rw [ite_eq_right (by omega : ¬ 2 ≤ (0 : ℕ))]
      rw [hMid, hLo, hLo2, ite_eq_left rfl, ite_eq_left rfl]
      rw [sub_zero]
      have h00 := hDiag 0
      linarith [h00]
    | succ j =>
      have hJS : j + 1 = j + 1 := rfl
      have hMid : (if 1 ≤ (0 : ℕ) ∧ 1 ≤ j + 1 then L (0 - 1) (j + 1 - 1)
          else 0) = 0 := by
        rw [ite_eq_right (by omega : ¬ (1 ≤ (0 : ℕ) ∧ 1 ≤ j + 1))]
      have hLo : (if 1 ≤ (0 : ℕ) then L (0 - 1) (j + 1) else 0) = 0 := by
        rw [ite_eq_right (by omega : ¬ 1 ≤ (0 : ℕ))]
      have hLo2 : (if 2 ≤ (0 : ℕ) then L (0 - 2) (j + 1) else 0) = 0 := by
        rw [ite_eq_right (by omega : ¬ 2 ≤ (0 : ℕ))]
      rw [hMid, hLo, hLo2, sub_zero]
      rw [ite_eq_right (by omega : ¬ j + 1 = 0)]
      have hT := hTri 0 (j + 1) (by omega)
      rw [hT]
      ring
  | succ m =>
    cases m with
    | zero =>
      have h10 : L 1 0 = -(r + lam) := by
        have hC := congrArg (fun Q => Polynomial.coeff Q 0) hp1
        rw [hPL 1 0, Polynomial.coeff_sub, Polynomial.coeff_X,
          Polynomial.coeff_C] at hC
        have h1 : ¬ (1 : ℕ) = 0 := by omega
        rw [ite_eq_right h1, ite_eq_left rfl] at hC
        rw [hlam] at hC
        linarith [hC]
      cases K with
      | zero =>
        have hMid : (if 1 ≤ (1 : ℕ) ∧ 1 ≤ 0 then L (1 - 1) (0 - 1) else 0) = 0 := by
          rw [ite_eq_right (by omega : ¬ (1 ≤ (1 : ℕ) ∧ 1 ≤ 0))]
        have hLo : (if 1 ≤ (1 : ℕ) then L (1 - 1) 0 else 0) = L 0 0 := by
          rw [ite_eq_left (by omega : 1 ≤ 1)]
        have hLo2 : (if 2 ≤ (1 : ℕ) then L (1 - 2) 0 else 0) = 0 := by
          rw [ite_eq_right (by omega : ¬ 2 ≤ (1 : ℕ))]
        have hK : (if (0 : ℕ) = 0 then
            (if (1 : ℕ) = 0 then (1 : ℝ) else if 1 = 1 then -lam
              else if 1 = 2 then -mu else 0) else 0) = -lam := by
          rw [ite_eq_left rfl, ite_eq_right (by omega : ¬ (1 : ℕ) = 0),
            ite_eq_left rfl]
        rw [hMid, hLo, hLo2, hK, sub_zero]
        have h00 := hDiag 0
        rw [h10, h00]
        ring
      | succ j =>
        have hMid : (if 1 ≤ (1 : ℕ) ∧ 1 ≤ j + 1 then L (1 - 1) (j + 1 - 1)
            else 0) = L 0 j := by
          rw [ite_eq_left ⟨by omega, by omega⟩]
          have e1 : (1 : ℕ) - 1 = 0 := by omega
          have e2 : j + 1 - 1 = j := by omega
          rw [e1, e2]
        have hLo : (if 1 ≤ (1 : ℕ) then L (1 - 1) (j + 1) else 0) = L 0 (j + 1) := by
          rw [ite_eq_left (by omega : 1 ≤ 1)]
        have hLo2 : (if 2 ≤ (1 : ℕ) then L (1 - 2) (j + 1) else 0) = 0 := by
          rw [ite_eq_right (by omega : ¬ 2 ≤ (1 : ℕ))]
        have hK : (if j + 1 = 0 then
            (if (1 : ℕ) = 0 then (1 : ℝ) else if 1 = 1 then -lam
              else if 1 = 2 then -mu else 0) else 0) = 0 := by
          rw [ite_eq_right (by omega : ¬ j + 1 = 0)]
        rw [hMid, hLo, hLo2, hK]
        by_cases hj : j = 0
        · rw [hj]
          have h11 := hDiag 1
          have h00 := hDiag 0
          have h01 : L 0 1 = 0 := hTri 0 1 (by omega)
          rw [h11, h01, h00]
          ring
        · have h1j : L 1 (j + 1) = 0 := hTri 1 (j + 1) (by omega)
          have h10j : L 0 (j + 1) = 0 := hTri 0 (j + 1) (by omega)
          have h0j : L 0 j = 0 := hTri 0 j (by omega)
          rw [h1j, h10j, h0j]
          ring
    | succ t =>
      cases t with
      | zero =>
        by_cases hk0 : K = 0
        · rw [hk0]
          have hFavN := hFav 0 0
          rw [ite_eq_left rfl] at hFavN
          have hα1 : α (0 + 1) = r := hrα 0
          have hβ1' : β (0 + 1) = s + mu := by
            have h01 : (0 : ℕ) + 1 = 1 := by omega
            rw [h01]
            exact hmu
          rw [hα1, hβ1'] at hFavN
          have hLo : (if 1 ≤ (2 : ℕ) then L (2 - 1) 0 else 0) = L 1 0 := by
            rw [ite_eq_left (by omega : 1 ≤ 2)]
          have hLo2 : (if 2 ≤ (2 : ℕ) then L (2 - 2) 0 else 0) = L 0 0 := by
            rw [ite_eq_left (by omega : 2 ≤ 2)]
          have hMid : (if 1 ≤ (2 : ℕ) ∧ 1 ≤ 0 then L (2 - 1) (0 - 1)
              else 0) = 0 := by
            rw [ite_eq_right (by omega : ¬ (1 ≤ (2 : ℕ) ∧ 1 ≤ 0))]
          have hK : (if (0 : ℕ) = 0 then
              (if (2 : ℕ) = 0 then (1 : ℝ) else if 2 = 1 then -lam
                else if 2 = 2 then -mu else 0) else 0) = -mu := by
            rw [ite_eq_left rfl, ite_eq_right (by omega : ¬ (2 : ℕ) = 0),
              ite_eq_right (by omega : ¬ (2 : ℕ) = 1), ite_eq_left rfl]
          rw [hLo, hLo2, hMid, hK, sub_zero]
          have h00 := hDiag 0
          have h02 : (0 : ℕ) + 2 = 2 := by omega
          rw [h02] at hFavN
          rw [h00] at hFavN ⊢
          linarith [hFavN]
        · have hFavN := hFav 0 K
          rw [ite_eq_right hk0] at hFavN
          have hα1 : α (0 + 1) = r := hrα 0
          have hβ1' : β (0 + 1) = s + mu := by
            have h01 : (0 : ℕ) + 1 = 1 := by omega
            rw [h01]
            exact hmu
          rw [hα1, hβ1'] at hFavN
          have hk1 : 1 ≤ K := by omega
          have hLo : (if 1 ≤ (2 : ℕ) then L (2 - 1) K else 0) = L 1 K := by
            rw [ite_eq_left (by omega : 1 ≤ 2)]
          have hLo2 : (if 2 ≤ (2 : ℕ) then L (2 - 2) K else 0) = L 0 K := by
            rw [ite_eq_left (by omega : 2 ≤ 2)]
          have hMid : (if 1 ≤ (2 : ℕ) ∧ 1 ≤ K then L (2 - 1) (K - 1)
              else 0) = L 1 (K - 1) := by
            rw [ite_eq_left ⟨by omega, hk1⟩]
          have hK : (if K = 0 then
              (if (2 : ℕ) = 0 then (1 : ℝ) else if 2 = 1 then -lam
                else if 2 = 2 then -mu else 0) else 0) = 0 := by
            rw [ite_eq_right hk0]
          rw [hLo, hLo2, hMid, hK]
          have h0K : L 0 K = 0 := hTri 0 K (by omega)
          have h02 : (0 : ℕ) + 2 = 2 := by omega
          rw [h02] at hFavN
          rw [h0K] at hFavN ⊢
          linarith [hFavN]
      | succ u =>
        by_cases hk0 : K = 0
        · rw [hk0]
          have hFavN := hFav (u + 1) 0
          rw [ite_eq_left rfl] at hFavN
          have hβN : β (u + 1 + 1) = s := by
            have hEq : u + 1 + 1 = u + 2 := by omega
            rw [hEq]
            cases u with
            | zero => exact hsβ 0
            | succ w =>
              have hEq2 : w + 1 + 2 = (w + 1) + 2 := by omega
              rw [hEq2]
              exact hsβ (w + 1)
          rw [hrα (u + 1), hβN] at hFavN
          have hLo : (if 1 ≤ u + 1 + 2 then L (u + 1 + 2 - 1) 0 else 0) =
              L (u + 1 + 1) 0 := by
            rw [ite_eq_left (by omega : 1 ≤ u + 1 + 2)]
            have e1 : u + 1 + 2 - 1 = u + 1 + 1 := by omega
            rw [e1]
          have hLo2 : (if 2 ≤ u + 1 + 2 then L (u + 1 + 2 - 2) 0 else 0) =
              L (u + 1) 0 := by
            rw [ite_eq_left (by omega : 2 ≤ u + 1 + 2)]
            have e2 : u + 1 + 2 - 2 = u + 1 := by omega
            rw [e2]
          have hMid : (if 1 ≤ u + 1 + 2 ∧ 1 ≤ 0 then L (u + 1 + 2 - 1) (0 - 1)
              else 0) = 0 := by
            rw [ite_eq_right (by omega : ¬ (1 ≤ u + 1 + 2 ∧ 1 ≤ 0))]
          have hK : (if (0 : ℕ) = 0 then
              (if u + 1 + 2 = 0 then (1 : ℝ) else if u + 1 + 2 = 1 then -lam
                else if u + 1 + 2 = 2 then -mu else 0) else 0) = 0 := by
            rw [ite_eq_left rfl, ite_eq_right (by omega : ¬ u + 1 + 2 = 0),
              ite_eq_right (by omega : ¬ u + 1 + 2 = 1),
              ite_eq_right (by omega : ¬ u + 1 + 2 = 2)]
          have hEq : u + 1 + 2 = (u + 1) + 2 := by omega
          rw [hLo, hLo2, hMid, hK, sub_zero]
          rw [hEq]
          linarith [hFavN]
        · have hFavN := hFav (u + 1) K
          have hk1 : 1 ≤ K := by omega
          rw [ite_eq_right hk0] at hFavN
          have hβN : β (u + 1 + 1) = s := by
            have hEq : u + 1 + 1 = u + 2 := by omega
            rw [hEq]
            cases u with
            | zero => exact hsβ 0
            | succ w =>
              have hEq2 : w + 1 + 2 = (w + 1) + 2 := by omega
              rw [hEq2]
              exact hsβ (w + 1)
          rw [hrα (u + 1), hβN] at hFavN
          have hLo : (if 1 ≤ u + 1 + 2 then L (u + 1 + 2 - 1) K else 0) =
              L (u + 1 + 1) K := by
            rw [ite_eq_left (by omega : 1 ≤ u + 1 + 2)]
            have e1 : u + 1 + 2 - 1 = u + 1 + 1 := by omega
            rw [e1]
          have hLo2 : (if 2 ≤ u + 1 + 2 then L (u + 1 + 2 - 2) K else 0) =
              L (u + 1) K := by
            rw [ite_eq_left (by omega : 2 ≤ u + 1 + 2)]
            have e2 : u + 1 + 2 - 2 = u + 1 := by omega
            rw [e2]
          have hMid : (if 1 ≤ u + 1 + 2 ∧ 1 ≤ K then L (u + 1 + 2 - 1) (K - 1)
              else 0) = L (u + 1 + 1) (K - 1) := by
            rw [ite_eq_left ⟨by omega, hk1⟩]
            have e1 : u + 1 + 2 - 1 = u + 1 + 1 := by omega
            rw [e1]
          have hK : (if K = 0 then
              (if u + 1 + 2 = 0 then (1 : ℝ) else if u + 1 + 2 = 1 then -lam
                else if u + 1 + 2 = 2 then -mu else 0) else 0) = 0 := by
            rw [ite_eq_right hk0]
          have hEq : u + 1 + 2 = (u + 1) + 2 := by omega
          rw [hLo, hLo2, hMid, hK]
          rw [hEq]
          linarith [hFavN]

/-- Stieltjes entries vanish above the superdiagonal. -/
private theorem stieltjes_eq_zero_of_gt (a1 b1 a b : ℝ) (j k : ℕ)
    (hk : k > j + 1) : stieltjesMatrix a1 b1 a b j k = 0 := by
  unfold stieltjesMatrix
  rw [ite_eq_right (by omega : ¬ k = j + 1)]
  have h2 : ¬ (j = 0 ∧ k = 0) := by omega
  rw [ite_eq_right h2]
  have h3 : ¬ (j = 1 ∧ k = 0) := by omega
  rw [ite_eq_right h3]
  have h4 : ¬ k = j := by omega
  rw [ite_eq_right h4]
  have h5 : ¬ k + 1 = j := by omega
  rw [ite_eq_right h5]

/-- Inverse array defined by the Stieltjes production recurrence. -/
private noncomputable def linvOf (r₁ s₁ r s : ℝ) : ℕ → ℕ → ℝ
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k => ∑ j ∈ Finset.range (n + 2),
      linvOf r₁ s₁ r s n j * stieltjesMatrix r₁ s₁ r s j k

/-- The production-defined inverse is lower-triangular. -/
private theorem linvOf_triangular (r₁ s₁ r s : ℝ) :
    ∀ n k : ℕ, k > n → linvOf r₁ s₁ r s n k = 0 := by
  intro n
  induction n with
  | zero =>
    intro k hk
    change (if k = 0 then (1 : ℝ) else 0) = 0
    rw [ite_eq_right (by omega : ¬ k = 0)]
  | succ m ih =>
    intro k hk
    change (∑ j ∈ Finset.range (m + 2),
      linvOf r₁ s₁ r s m j * stieltjesMatrix r₁ s₁ r s j k) = 0
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_range] at hj
    by_cases hjle : j ≤ m
    · have hS := stieltjes_eq_zero_of_gt r₁ s₁ r s j k (by omega)
      rw [hS, mul_zero]
    · have hjEq : j = m + 1 := by omega
      rw [hjEq]
      have hL := ih (m + 1) (by omega)
      rw [hL, zero_mul]

/-- Stieltjes superdiagonal is one. -/
private theorem stieltjes_succ (a1 b1 a b : ℝ) (m : ℕ) :
    stieltjesMatrix a1 b1 a b m (m + 1) = 1 := by
  unfold stieltjesMatrix
  rw [ite_eq_left rfl]

/-- Stieltjes `(1, 1)` and `(1, 2)` entries. -/
private theorem stieltjes_one_one (a1 b1 a b : ℝ) :
    stieltjesMatrix a1 b1 a b 1 1 = a := by
  simp [stieltjesMatrix]

private theorem stieltjes_one_two (a1 b1 a b : ℝ) :
    stieltjesMatrix a1 b1 a b 1 2 = 1 := by
  simp [stieltjesMatrix]

/-- The recurrence determines `L 1 0`. -/
private theorem recurrence_L10 (L : ℕ → ℕ → ℝ)
    (lam mu r s : ℝ)
    (hRec : ∀ N K : ℕ,
      L N K + r * (if 1 ≤ N then L (N - 1) K else 0) -
          (if 1 ≤ N ∧ 1 ≤ K then L (N - 1) (K - 1) else 0) +
          s * (if 2 ≤ N then L (N - 2) K else 0) =
        (if K = 0 then
          if N = 0 then 1 else if N = 1 then -lam else if N = 2 then -mu else 0
        else 0))
    (h00 : L 0 0 = 1) :
    L 1 0 = -(r + lam) := by
  have hR := hRec 1 0
  have hMid : (if 1 ≤ (1 : ℕ) ∧ 1 ≤ 0 then L (1 - 1) (0 - 1) else 0) = 0 := by
    rw [ite_eq_right (by omega : ¬ (1 ≤ (1 : ℕ) ∧ 1 ≤ 0))]
  have hLo : (if 1 ≤ (1 : ℕ) then L (1 - 1) 0 else 0) = L 0 0 := by
    rw [ite_eq_left (by omega : 1 ≤ 1)]
  have hLo2 : (if 2 ≤ (1 : ℕ) then L (1 - 2) 0 else 0) = 0 := by
    rw [ite_eq_right (by omega : ¬ 2 ≤ (1 : ℕ))]
  have hK : (if (0 : ℕ) = 0 then
      (if (1 : ℕ) = 0 then (1 : ℝ) else if 1 = 1 then -lam
        else if 1 = 2 then -mu else 0) else 0) = -lam := by
    rw [ite_eq_left rfl, ite_eq_right (by omega : ¬ (1 : ℕ) = 0),
      ite_eq_left rfl]
  rw [hMid, hLo, hLo2, hK, h00] at hR
  linarith [hR]

/-- First row of the production inverse. -/
private theorem linvOf_one (r₁ s₁ r s : ℝ) (k : ℕ) :
    linvOf r₁ s₁ r s 1 k = stieltjesMatrix r₁ s₁ r s 0 k := by
  change (∑ j ∈ Finset.range (0 + 2),
    linvOf r₁ s₁ r s 0 j * stieltjesMatrix r₁ s₁ r s j k) = _
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  change ((0 : ℝ) + linvOf r₁ s₁ r s 0 0 * stieltjesMatrix r₁ s₁ r s 0 k +
    linvOf r₁ s₁ r s 0 1 * stieltjesMatrix r₁ s₁ r s 1 k) = _
  have h00 : linvOf r₁ s₁ r s 0 0 = 1 := by
    change (if (0 : ℕ) = 0 then (1 : ℝ) else 0) = 1
    rw [ite_eq_left rfl]
  have h01 : linvOf r₁ s₁ r s 0 1 = 0 := by
    change (if (1 : ℕ) = 0 then (1 : ℝ) else 0) = 0
    rw [ite_eq_right (by omega : ¬ (1 : ℕ) = 0)]
  rw [h00, h01, zero_add, one_mul, zero_mul, add_zero]

/-- Left-inverse base case `n = 0`. -/
private theorem linvOf_left_base_zero (L : ℕ → ℕ → ℝ)
    (r₁ s₁ r s : ℝ) (h00 : L 0 0 = 1) (k : ℕ) :
    (∑ j ∈ Finset.range (0 + 1), L 0 j * linvOf r₁ s₁ r s j k) =
      (if 0 = k then 1 else 0) := by
  rw [Finset.sum_range_one]
  have hL : L 0 0 = 1 := h00
  have hM : linvOf r₁ s₁ r s 0 k = (if 0 = k then 1 else 0) := by
    change (if k = 0 then (1 : ℝ) else 0) = _
    by_cases hk : k = 0
    · rw [ite_eq_left hk, ite_eq_left hk.symm]
    · have hk' : ¬ (0 : ℕ) = k := by omega
      rw [ite_eq_right hk, ite_eq_right hk']
  rw [hL, hM]
  by_cases hk : (0 : ℕ) = k
  · rw [ite_eq_left hk, one_mul]
  · rw [ite_eq_right hk, one_mul]

/-- Left-inverse base case `n = 1`. -/
private theorem linvOf_left_base_one (L : ℕ → ℕ → ℝ)
    (lam mu r s : ℝ)
    (hRec : ∀ N K : ℕ,
      L N K + r * (if 1 ≤ N then L (N - 1) K else 0) -
          (if 1 ≤ N ∧ 1 ≤ K then L (N - 1) (K - 1) else 0) +
          s * (if 2 ≤ N then L (N - 2) K else 0) =
        (if K = 0 then
          if N = 0 then 1 else if N = 1 then -lam else if N = 2 then -mu else 0
        else 0))
    (h00 : L 0 0 = 1) (h11 : L 1 1 = 1) (k : ℕ) :
    (∑ j ∈ Finset.range (1 + 1), L 1 j * linvOf (r + lam) (s + mu) r s j k) =
      (if 1 = k then 1 else 0) := by
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  have h10 : L 1 0 = -(r + lam) := recurrence_L10 L lam mu r s hRec h00
  have hM0 : linvOf (r + lam) (s + mu) r s 0 k = (if 0 = k then 1 else 0) := by
    change (if k = 0 then (1 : ℝ) else 0) = _
    by_cases hk : k = 0
    · rw [ite_eq_left hk, ite_eq_left hk.symm]
    · have hk' : ¬ (0 : ℕ) = k := by omega
      rw [ite_eq_right hk, ite_eq_right hk']
  have hM1 : linvOf (r + lam) (s + mu) r s 1 k =
      stieltjesMatrix (r + lam) (s + mu) r s 0 k :=
    linvOf_one (r + lam) (s + mu) r s k
  rw [h10, h11, hM0, hM1]
  by_cases hk0 : k = 0
  · rw [hk0]
    have hS : stieltjesMatrix (r + lam) (s + mu) r s 0 0 = r + lam :=
      stieltjes_zero_zero (r + lam) (s + mu) r s
    rw [hS]
    have h10k : (if (0 : ℕ) = 0 then (1 : ℝ) else 0) = 1 := by
      rw [ite_eq_left rfl]
    have h1k : (if (1 : ℕ) = 0 then (1 : ℝ) else 0) = 0 := by
      rw [ite_eq_right (by omega : ¬ (1 : ℕ) = 0)]
    rw [h10k, h1k]
    ring
  · by_cases hk1 : k = 1
    · rw [hk1]
      have hS : stieltjesMatrix (r + lam) (s + mu) r s 0 1 = 1 :=
        stieltjes_zero_one (r + lam) (s + mu) r s
      rw [hS]
      have h10k : (if (0 : ℕ) = 1 then (1 : ℝ) else 0) = 0 := by
        rw [ite_eq_right (by omega : ¬ (0 : ℕ) = 1)]
      have h1k : (if (1 : ℕ) = 1 then (1 : ℝ) else 0) = 1 := by
        rw [ite_eq_left rfl]
      rw [h10k, h1k]
      ring
    · have hS : stieltjesMatrix (r + lam) (s + mu) r s 0 k = 0 :=
        stieltjes_eq_zero_of_gt (r + lam) (s + mu) r s 0 k (by omega)
      rw [hS]
      have h10k : (if (0 : ℕ) = k then (1 : ℝ) else 0) = 0 := by
        rw [ite_eq_right (by omega : ¬ (0 : ℕ) = k)]
      have h1k : (if (1 : ℕ) = k then (1 : ℝ) else 0) = 0 := by
        rw [ite_eq_right (by omega : ¬ (1 : ℕ) = k)]
      rw [h10k, h1k]
      ring

/-- Shift sum via production equals a Stieltjes entry. -/
private theorem linvOf_shift_sum (r₁ s₁ r s : ℝ) (L : ℕ → ℕ → ℝ)
    (n : ℕ) (k : ℕ)
    (hIH : ∀ t : ℕ, (∑ i ∈ Finset.range (n + 2), L (n + 1) i *
      linvOf r₁ s₁ r s i t) = (if n + 1 = t then 1 else 0)) :
    (∑ i ∈ Finset.range (n + 2), L (n + 1) i *
      linvOf r₁ s₁ r s (i + 1) k) =
      stieltjesMatrix r₁ s₁ r s (n + 1) k := by
  have hProd : ∀ i k : ℕ, linvOf r₁ s₁ r s (i + 1) k =
      ∑ t ∈ Finset.range (i + 2),
        linvOf r₁ s₁ r s i t * stieltjesMatrix r₁ s₁ r s t k := fun i k => rfl
  have hTriM := linvOf_triangular r₁ s₁ r s
  have hExt : ∀ i ∈ Finset.range (n + 2),
      (∑ t ∈ Finset.range (i + 2),
        linvOf r₁ s₁ r s i t * stieltjesMatrix r₁ s₁ r s t k) =
      ∑ t ∈ Finset.range (n + 3),
        linvOf r₁ s₁ r s i t * stieltjesMatrix r₁ s₁ r s t k := by
    intro i hi
    rw [Finset.mem_range] at hi
    apply Finset.sum_subset
    · intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    · intro t _ hni
      rw [Finset.mem_range] at hni
      push Not at hni
      have hM : linvOf r₁ s₁ r s i t = 0 := hTriM i t (by omega)
      rw [hM, zero_mul]
  have hStep1 : (∑ i ∈ Finset.range (n + 2), L (n + 1) i *
      linvOf r₁ s₁ r s (i + 1) k) =
      ∑ i ∈ Finset.range (n + 2), ∑ t ∈ Finset.range (n + 3),
        L (n + 1) i * (linvOf r₁ s₁ r s i t *
          stieltjesMatrix r₁ s₁ r s t k) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hProd i k, hExt i hi, Finset.mul_sum]
  rw [hStep1, Finset.sum_comm]
  have hStep2 : (∑ t ∈ Finset.range (n + 3), ∑ i ∈ Finset.range (n + 2),
      L (n + 1) i * (linvOf r₁ s₁ r s i t *
        stieltjesMatrix r₁ s₁ r s t k)) =
      ∑ t ∈ Finset.range (n + 3),
        (∑ i ∈ Finset.range (n + 2), L (n + 1) i * linvOf r₁ s₁ r s i t) *
        stieltjesMatrix r₁ s₁ r s t k := by
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hStep2]
  have hStep3 : (∑ t ∈ Finset.range (n + 3),
      (∑ i ∈ Finset.range (n + 2), L (n + 1) i * linvOf r₁ s₁ r s i t) *
      stieltjesMatrix r₁ s₁ r s t k) =
      ∑ t ∈ Finset.range (n + 3),
        (if n + 1 = t then 1 else 0) *
        stieltjesMatrix r₁ s₁ r s t k := by
    apply Finset.sum_congr rfl
    intro t _
    rw [hIH t]
  rw [hStep3]
  have hStep4 : (∑ t ∈ Finset.range (n + 3),
      (if n + 1 = t then 1 else 0) *
      stieltjesMatrix r₁ s₁ r s t k) =
      stieltjesMatrix r₁ s₁ r s (n + 1) k := by
    have hEq : (∑ t ∈ Finset.range (n + 3),
        (if n + 1 = t then 1 else 0) *
        stieltjesMatrix r₁ s₁ r s t k) =
        ∑ t ∈ Finset.range (n + 3),
          (if n + 1 = t then stieltjesMatrix r₁ s₁ r s t k else 0) := by
      apply Finset.sum_congr rfl
      intro t _
      by_cases ht : n + 1 = t
      · rw [ite_eq_left ht, ite_eq_left ht, one_mul]
      · rw [ite_eq_right ht, ite_eq_right ht, zero_mul]
    rw [hEq, Finset.sum_ite_eq]
    have hMem : n + 1 ∈ Finset.range (n + 3) := by
      rw [Finset.mem_range]; omega
    rw [ite_eq_left hMem]
  exact hStep4


/-- Second row of the production inverse. -/
private theorem linvOf_two (r₁ s₁ r s : ℝ) (k : ℕ) :
    linvOf r₁ s₁ r s 2 k = r₁ * stieltjesMatrix r₁ s₁ r s 0 k +
      stieltjesMatrix r₁ s₁ r s 1 k := by
  have hDef : linvOf r₁ s₁ r s 2 k = ∑ t ∈ Finset.range (1 + 2),
      linvOf r₁ s₁ r s 1 t * stieltjesMatrix r₁ s₁ r s t k := rfl
  rw [hDef]
  have h1 : ∀ t : ℕ, linvOf r₁ s₁ r s 1 t =
      stieltjesMatrix r₁ s₁ r s 0 t := fun t => linvOf_one r₁ s₁ r s t
  rw [Finset.sum_congr rfl (fun t _ => by rw [h1 t])]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  have hS00 : stieltjesMatrix r₁ s₁ r s 0 0 = r₁ :=
    stieltjes_zero_zero r₁ s₁ r s
  have hS01 : stieltjesMatrix r₁ s₁ r s 0 1 = 1 :=
    stieltjes_zero_one r₁ s₁ r s
  have hS02 : stieltjesMatrix r₁ s₁ r s 0 2 = 0 :=
    stieltjes_eq_zero_of_gt r₁ s₁ r s 0 2 (by omega)
  rw [hS00, hS01, hS02]
  ring

/-- Left-inverse at `n = 2` by direct expansion. -/
private theorem linvOf_left_two (L : ℕ → ℕ → ℝ)
    (hTri : ∀ n k : ℕ, n < k → L n k = 0)
    (lam mu r s : ℝ)
    (hRec : ∀ N K : ℕ,
      L N K + r * (if 1 ≤ N then L (N - 1) K else 0) -
          (if 1 ≤ N ∧ 1 ≤ K then L (N - 1) (K - 1) else 0) +
          s * (if 2 ≤ N then L (N - 2) K else 0) =
        (if K = 0 then
          if N = 0 then 1 else if N = 1 then -lam else if N = 2 then -mu else 0
        else 0))
    (h00 : L 0 0 = 1) (h11 : L 1 1 = 1) (k : ℕ) :
    (∑ j ∈ Finset.range (2 + 1), L 2 j *
      linvOf (r + lam) (s + mu) r s j k) = (if 2 = k then 1 else 0) := by
  have h10 : L 1 0 = -(r + lam) := recurrence_L10 L lam mu r s hRec h00
  have h12 : L 1 2 = 0 := hTri 1 2 (by omega)
  have h01 : L 0 1 = 0 := hTri 0 1 (by omega)
  have h02 : L 0 2 = 0 := hTri 0 2 (by omega)
  have hL20 : L 2 0 = -r * L 1 0 - s * L 0 0 + (-mu) := by
    have hR := hRec 2 0
    have hLo : (if 1 ≤ (2 : ℕ) then L (2 - 1) 0 else 0) = L 1 0 := by
      rw [ite_eq_left (by omega : 1 ≤ 2)]
    have hLo2 : (if 2 ≤ (2 : ℕ) then L (2 - 2) 0 else 0) = L 0 0 := by
      rw [ite_eq_left (by omega : 2 ≤ 2)]
    have hMid : (if 1 ≤ (2 : ℕ) ∧ 1 ≤ 0 then L (2 - 1) (0 - 1) else 0) = 0 := by
      rw [ite_eq_right (by omega : ¬ (1 ≤ (2 : ℕ) ∧ 1 ≤ 0))]
    have hK : (if (0 : ℕ) = 0 then
        (if (2 : ℕ) = 0 then (1 : ℝ) else if 2 = 1 then -lam
          else if 2 = 2 then -mu else 0) else 0) = -mu := by
      rw [ite_eq_left rfl, ite_eq_right (by omega : ¬ (2 : ℕ) = 0),
        ite_eq_right (by omega : ¬ (2 : ℕ) = 1), ite_eq_left rfl]
    rw [hLo, hLo2, hMid, hK] at hR
    linarith [hR]
  have hL21 : L 2 1 = -r * L 1 1 + L 1 0 - s * L 0 1 := by
    have hR := hRec 2 1
    have hLo : (if 1 ≤ (2 : ℕ) then L (2 - 1) 1 else 0) = L 1 1 := by
      rw [ite_eq_left (by omega : 1 ≤ 2)]
    have hLo2 : (if 2 ≤ (2 : ℕ) then L (2 - 2) 1 else 0) = L 0 1 := by
      rw [ite_eq_left (by omega : 2 ≤ 2)]
    have hMid : (if 1 ≤ (2 : ℕ) ∧ 1 ≤ 1 then L (2 - 1) (1 - 1) else 0) =
        L 1 0 := by
      rw [ite_eq_left ⟨by omega, by omega⟩]
    have hK : (if (1 : ℕ) = 0 then
        (if (2 : ℕ) = 0 then (1 : ℝ) else if 2 = 1 then -lam
          else if 2 = 2 then -mu else 0) else 0) = 0 := by
      rw [ite_eq_right (by omega : ¬ (1 : ℕ) = 0)]
    rw [hLo, hLo2, hMid, hK] at hR
    linarith [hR]
  have hL22 : L 2 2 = -r * L 1 2 + L 1 1 - s * L 0 2 := by
    have hR := hRec 2 2
    have hLo : (if 1 ≤ (2 : ℕ) then L (2 - 1) 2 else 0) = L 1 2 := by
      rw [ite_eq_left (by omega : 1 ≤ 2)]
    have hLo2 : (if 2 ≤ (2 : ℕ) then L (2 - 2) 2 else 0) = L 0 2 := by
      rw [ite_eq_left (by omega : 2 ≤ 2)]
    have hMid : (if 1 ≤ (2 : ℕ) ∧ 1 ≤ 2 then L (2 - 1) (2 - 1) else 0) =
        L 1 1 := by
      rw [ite_eq_left ⟨by omega, by omega⟩]
    have hK : (if (2 : ℕ) = 0 then
        (if (2 : ℕ) = 0 then (1 : ℝ) else if 2 = 1 then -lam
          else if 2 = 2 then -mu else 0) else 0) = 0 := by
      rw [ite_eq_right (by omega : ¬ (2 : ℕ) = 0)]
    rw [hLo, hLo2, hMid, hK] at hR
    linarith [hR]
  have hM0 : linvOf (r + lam) (s + mu) r s 0 k =
      (if k = 0 then 1 else 0) := rfl
  have hM1 : linvOf (r + lam) (s + mu) r s 1 k =
      stieltjesMatrix (r + lam) (s + mu) r s 0 k :=
    linvOf_one (r + lam) (s + mu) r s k
  have hM2 : linvOf (r + lam) (s + mu) r s 2 k =
      (r + lam) * stieltjesMatrix (r + lam) (s + mu) r s 0 k +
      stieltjesMatrix (r + lam) (s + mu) r s 1 k :=
    linvOf_two (r + lam) (s + mu) r s k
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  rw [hL20, hL21, hL22, hM0, hM1, hM2, h10, h11, h12, h01, h02, h00]
  by_cases hk0 : k = 0
  · rw [hk0]
    have hS00 : stieltjesMatrix (r + lam) (s + mu) r s 0 0 = r + lam :=
      stieltjes_zero_zero (r + lam) (s + mu) r s
    have hS10 : stieltjesMatrix (r + lam) (s + mu) r s 1 0 = s + mu :=
      stieltjes_one_zero (r + lam) (s + mu) r s
    rw [hS00, hS10]
    have e1 : (if (0 : ℕ) = 0 then (1 : ℝ) else 0) = 1 := by
      rw [ite_eq_left rfl]
    have e2 : (if (2 : ℕ) = 0 then (1 : ℝ) else 0) = 0 := by
      rw [ite_eq_right (by omega : ¬ (2 : ℕ) = 0)]
    rw [e1, e2]
    ring
  · by_cases hk1 : k = 1
    · rw [hk1]
      have hS01 : stieltjesMatrix (r + lam) (s + mu) r s 0 1 = 1 :=
        stieltjes_zero_one (r + lam) (s + mu) r s
      have hS11 : stieltjesMatrix (r + lam) (s + mu) r s 1 1 = r :=
        stieltjes_one_one (r + lam) (s + mu) r s
      rw [hS01, hS11]
      have e1 : (if (1 : ℕ) = 0 then (1 : ℝ) else 0) = 0 := by
        rw [ite_eq_right (by omega : ¬ (1 : ℕ) = 0)]
      have e2 : (if (2 : ℕ) = 1 then (1 : ℝ) else 0) = 0 := by
        rw [ite_eq_right (by omega : ¬ (2 : ℕ) = 1)]
      rw [e1, e2]
      ring
    · by_cases hk2 : k = 2
      · rw [hk2]
        have hS02 : stieltjesMatrix (r + lam) (s + mu) r s 0 2 = 0 :=
          stieltjes_eq_zero_of_gt (r + lam) (s + mu) r s 0 2 (by omega)
        have hS12 : stieltjesMatrix (r + lam) (s + mu) r s 1 2 = 1 :=
          stieltjes_one_two (r + lam) (s + mu) r s
        rw [hS02, hS12]
        have e1 : (if (2 : ℕ) = 0 then (1 : ℝ) else 0) = 0 := by
          rw [ite_eq_right (by omega : ¬ (2 : ℕ) = 0)]
        have e2 : (if (2 : ℕ) = 2 then (1 : ℝ) else 0) = 1 := by
          rw [ite_eq_left rfl]
        rw [e1, e2]
        ring
      · have hS0k : stieltjesMatrix (r + lam) (s + mu) r s 0 k = 0 :=
          stieltjes_eq_zero_of_gt (r + lam) (s + mu) r s 0 k (by omega)
        have hS1k : stieltjesMatrix (r + lam) (s + mu) r s 1 k = 0 :=
          stieltjes_eq_zero_of_gt (r + lam) (s + mu) r s 1 k (by omega)
        rw [hS0k, hS1k]
        have e1 : (if k = 0 then (1 : ℝ) else 0) = 0 := by
          rw [ite_eq_right hk0]
        have e2 : (if (2 : ℕ) = k then (1 : ℝ) else 0) = 0 := by
          rw [ite_eq_right (by omega : ¬ (2 : ℕ) = k)]
        rw [e1, e2]
        ring

/-- Stieltjes rows `≥ 2` use only bulk parameters. -/
private theorem stieltjes_ge_two (r₁ s₁ r s : ℝ) (m k : ℕ) (hm : 2 ≤ m) :
    stieltjesMatrix r₁ s₁ r s m k =
      (if k = m + 1 then 1 else if k = m then r
        else if k + 1 = m then s else 0) := by
  unfold stieltjesMatrix
  by_cases hk : k = m + 1
  · rw [ite_eq_left hk, ite_eq_left hk]
  · rw [ite_eq_right hk, ite_eq_right hk]
    have h2 : ¬ (m = 0 ∧ k = 0) := by omega
    have h3 : ¬ (m = 1 ∧ k = 0) := by omega
    rw [ite_eq_right h2, ite_eq_right h3]

/-- Stieltjes step identity for the left-inverse induction. -/
private theorem stieltjes_step_eq (r₁ s₁ r s : ℝ) (n k : ℕ) (hn : 1 ≤ n) :
    -r * (if n + 1 = k then (1 : ℝ) else 0) +
      stieltjesMatrix r₁ s₁ r s (n + 1) k -
      s * (if n = k then (1 : ℝ) else 0) =
      (if n + 2 = k then 1 else 0) := by
  have hS := stieltjes_ge_two r₁ s₁ r s (n + 1) k (by omega)
  rw [hS]
  by_cases hk2 : n + 2 = k
  · have e1 : (if n + 1 = k then (1 : ℝ) else 0) = 0 := by
      rw [ite_eq_right (by omega : ¬ n + 1 = k)]
    have e2 : (if n = k then (1 : ℝ) else 0) = 0 := by
      rw [ite_eq_right (by omega : ¬ n = k)]
    have e4 : (if n + 2 = k then (1 : ℝ) else 0) = 1 := by
      rw [ite_eq_left hk2]
    have hk2' : k = n + 1 + 1 := by omega
    rw [e1, e2, e4, ite_eq_left hk2']
    ring
  · by_cases hk1 : n + 1 = k
    · have e1 : (if n + 1 = k then (1 : ℝ) else 0) = 1 := by
        rw [ite_eq_left hk1]
      have e2 : (if n = k then (1 : ℝ) else 0) = 0 := by
        rw [ite_eq_right (by omega : ¬ n = k)]
      have e5 : (if n + 2 = k then (1 : ℝ) else 0) = 0 := by
        rw [ite_eq_right hk2]
      have hk1' : k = n + 1 := by omega
      rw [e1, e2, e5, ite_eq_right (by omega : ¬ k = n + 1 + 1),
        ite_eq_left hk1']
      ring
    · by_cases hk0 : n = k
      · have e1 : (if n + 1 = k then (1 : ℝ) else 0) = 0 := by
          rw [ite_eq_right hk1]
        have e2 : (if n = k then (1 : ℝ) else 0) = 1 := by
          rw [ite_eq_left hk0]
        have e5 : (if n + 2 = k then (1 : ℝ) else 0) = 0 := by
          rw [ite_eq_right hk2]
        have hk0' : k + 1 = n + 1 := by omega
        rw [e1, e2, e5, ite_eq_right (by omega : ¬ k = n + 1 + 1),
          ite_eq_right (by omega : ¬ k = n + 1), ite_eq_left hk0']
        ring
      · have e1 : (if n + 1 = k then (1 : ℝ) else 0) = 0 := by
          rw [ite_eq_right hk1]
        have e2 : (if n = k then (1 : ℝ) else 0) = 0 := by
          rw [ite_eq_right hk0]
        have e5 : (if n + 2 = k then (1 : ℝ) else 0) = 0 := by
          rw [ite_eq_right hk2]
        rw [e1, e2, e5, ite_eq_right (by omega : ¬ k = n + 1 + 1),
          ite_eq_right (by omega : ¬ k = n + 1),
          ite_eq_right (by omega : ¬ k + 1 = n + 1)]
        ring

/-- Left-inverse induction step for `n ≥ 1`. -/
private theorem linvOf_left_step (L : ℕ → ℕ → ℝ)
    (hTri : ∀ n k : ℕ, n < k → L n k = 0)
    (lam mu r s : ℝ)
    (hRec : ∀ N K : ℕ,
      L N K + r * (if 1 ≤ N then L (N - 1) K else 0) -
          (if 1 ≤ N ∧ 1 ≤ K then L (N - 1) (K - 1) else 0) +
          s * (if 2 ≤ N then L (N - 2) K else 0) =
        (if K = 0 then
          if N = 0 then 1 else if N = 1 then -lam else if N = 2 then -mu else 0
        else 0))
    (n : ℕ) (hn : 1 ≤ n)
    (hPn : ∀ t : ℕ, (∑ i ∈ Finset.range (n + 1), L n i *
      linvOf (r + lam) (s + mu) r s i t) = (if n = t then 1 else 0))
    (hPn1 : ∀ t : ℕ, (∑ i ∈ Finset.range (n + 2), L (n + 1) i *
      linvOf (r + lam) (s + mu) r s i t) = (if n + 1 = t then 1 else 0))
    (k : ℕ) :
    (∑ j ∈ Finset.range (n + 2 + 1), L (n + 2) j *
      linvOf (r + lam) (s + mu) r s j k) =
      (if n + 2 = k then 1 else 0) := by
  have hD : ∀ j ∈ Finset.range (n + 2 + 1), L (n + 2) j =
      -r * L (n + 1) j + (if 1 ≤ j then L (n + 1) (j - 1) else 0) -
        s * L n j := by
    intro j _
    have hR := hRec (n + 2) j
    have hN1 : (1 : ℕ) ≤ n + 2 := by omega
    have hN2 : (2 : ℕ) ≤ n + 2 := by omega
    have hLo : (if 1 ≤ n + 2 then L (n + 2 - 1) j else 0) = L (n + 1) j := by
      rw [ite_eq_left hN1]
      have e1 : n + 2 - 1 = n + 1 := by omega
      rw [e1]
    have hLo2 : (if 2 ≤ n + 2 then L (n + 2 - 2) j else 0) = L n j := by
      rw [ite_eq_left hN2]
      have e2 : n + 2 - 2 = n := by omega
      rw [e2]
    have hMid : (if 1 ≤ n + 2 ∧ 1 ≤ j then L (n + 2 - 1) (j - 1) else 0) =
        (if 1 ≤ j then L (n + 1) (j - 1) else 0) := by
      by_cases hj : 1 ≤ j
      · rw [ite_eq_left ⟨hN1, hj⟩, ite_eq_left hj]
        have e1 : n + 2 - 1 = n + 1 := by omega
        rw [e1]
      · rw [ite_eq_right (by omega : ¬ (1 ≤ n + 2 ∧ 1 ≤ j)),
          ite_eq_right hj]
    have hK : (if j = 0 then
        (if n + 2 = 0 then (1 : ℝ) else if n + 2 = 1 then -lam
          else if n + 2 = 2 then -mu else 0) else 0) = 0 := by
      by_cases hj : j = 0
      · rw [ite_eq_left hj, ite_eq_right (by omega : ¬ n + 2 = 0),
          ite_eq_right (by omega : ¬ n + 2 = 1),
          ite_eq_right (by omega : ¬ n + 2 = 2)]
      · rw [ite_eq_right hj]
    rw [hLo, hLo2, hMid, hK] at hR
    linarith [hR]
  have hDist : ∀ j ∈ Finset.range (n + 2 + 1),
      L (n + 2) j * linvOf (r + lam) (s + mu) r s j k =
      (-r * L (n + 1) j * linvOf (r + lam) (s + mu) r s j k +
        (if 1 ≤ j then L (n + 1) (j - 1) else 0) *
          linvOf (r + lam) (s + mu) r s j k) -
      s * L n j * linvOf (r + lam) (s + mu) r s j k := by
    intro j hj
    rw [hD j hj]
    ring
  rw [Finset.sum_congr rfl hDist, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  have hA : (∑ j ∈ Finset.range (n + 2 + 1),
      -r * L (n + 1) j * linvOf (r + lam) (s + mu) r s j k) =
      -r * (if n + 1 = k then 1 else 0) := by
    have hTrunc : (∑ j ∈ Finset.range (n + 2 + 1), L (n + 1) j *
        linvOf (r + lam) (s + mu) r s j k) =
        ∑ j ∈ Finset.range (n + 2), L (n + 1) j *
          linvOf (r + lam) (s + mu) r s j k := by
      rw [Finset.sum_range_succ]
      have hTop : L (n + 1) (n + 2) *
          linvOf (r + lam) (s + mu) r s (n + 2) k = 0 := by
        have hT := hTri (n + 1) (n + 2) (by omega)
        rw [hT, zero_mul]
      rw [hTop, add_zero]
    have hMul : (∑ j ∈ Finset.range (n + 2 + 1),
        -r * L (n + 1) j * linvOf (r + lam) (s + mu) r s j k) =
        -r * ∑ j ∈ Finset.range (n + 2 + 1), L (n + 1) j *
          linvOf (r + lam) (s + mu) r s j k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hMul, hTrunc, hPn1 k]
  have hC : (∑ j ∈ Finset.range (n + 2 + 1),
      s * L n j * linvOf (r + lam) (s + mu) r s j k) =
      s * (if n = k then 1 else 0) := by
    have hTrunc : (∑ j ∈ Finset.range (n + 2 + 1), L n j *
        linvOf (r + lam) (s + mu) r s j k) =
        ∑ j ∈ Finset.range (n + 1), L n j *
          linvOf (r + lam) (s + mu) r s j k := by
      rw [Finset.sum_range_succ]
      have hTop2 : L n (n + 2) *
          linvOf (r + lam) (s + mu) r s (n + 2) k = 0 := by
        have hT := hTri n (n + 2) (by omega)
        rw [hT, zero_mul]
      rw [hTop2, add_zero]
      have hEq : n + 2 = (n + 1) + 1 := by omega
      rw [hEq, Finset.sum_range_succ]
      have hTop1 : L n (n + 1) *
          linvOf (r + lam) (s + mu) r s (n + 1) k = 0 := by
        have hT := hTri n (n + 1) (by omega)
        rw [hT, zero_mul]
      rw [hTop1, add_zero]
    have hMul : (∑ j ∈ Finset.range (n + 2 + 1),
        s * L n j * linvOf (r + lam) (s + mu) r s j k) =
        s * ∑ j ∈ Finset.range (n + 2 + 1), L n j *
          linvOf (r + lam) (s + mu) r s j k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hMul, hTrunc, hPn k]
  have hB : (∑ j ∈ Finset.range (n + 2 + 1),
      (if 1 ≤ j then L (n + 1) (j - 1) else 0) *
        linvOf (r + lam) (s + mu) r s j k) =
      stieltjesMatrix (r + lam) (s + mu) r s (n + 1) k := by
    have hReidx : (∑ j ∈ Finset.range (n + 2 + 1),
        (if 1 ≤ j then L (n + 1) (j - 1) else 0) *
          linvOf (r + lam) (s + mu) r s j k) =
        ∑ i ∈ Finset.range (n + 2), L (n + 1) i *
          linvOf (r + lam) (s + mu) r s (i + 1) k := by
      rw [Finset.sum_range_succ']
      have h0 : (if 1 ≤ (0 : ℕ) then L (n + 1) (0 - 1) else 0) *
          linvOf (r + lam) (s + mu) r s 0 k = 0 := by
        rw [ite_eq_right (by omega : ¬ 1 ≤ (0 : ℕ)), zero_mul]
      rw [h0, add_zero]
      apply Finset.sum_congr rfl
      intro i _
      rw [ite_eq_left (by omega : 1 ≤ i + 1)]
      have hi : i + 1 - 1 = i := by omega
      rw [hi]
    rw [hReidx]
    exact linvOf_shift_sum (r + lam) (s + mu) r s L n k hPn1
  rw [hA, hB, hC]
  exact stieltjes_step_eq (r + lam) (s + mu) r s n k hn

/-- Full left-inverse from the recurrence. -/
private theorem linvOf_left_all (L : ℕ → ℕ → ℝ)
    (hTri : ∀ n k : ℕ, n < k → L n k = 0)
    (lam mu r s : ℝ)
    (hRec : ∀ N K : ℕ,
      L N K + r * (if 1 ≤ N then L (N - 1) K else 0) -
          (if 1 ≤ N ∧ 1 ≤ K then L (N - 1) (K - 1) else 0) +
          s * (if 2 ≤ N then L (N - 2) K else 0) =
        (if K = 0 then
          if N = 0 then 1 else if N = 1 then -lam else if N = 2 then -mu else 0
        else 0))
    (h00 : L 0 0 = 1) (h11 : L 1 1 = 1) :
    ∀ n k : ℕ, (∑ j ∈ Finset.range (n + 1), L n j *
      linvOf (r + lam) (s + mu) r s j k) = (if n = k then 1 else 0) := by
  have base0 : ∀ k : ℕ, (∑ j ∈ Finset.range (0 + 1), L 0 j *
      linvOf (r + lam) (s + mu) r s j k) = (if 0 = k then 1 else 0) :=
    fun k => linvOf_left_base_zero L (r + lam) (s + mu) r s h00 k
  have base1 : ∀ k : ℕ, (∑ j ∈ Finset.range (1 + 1), L 1 j *
      linvOf (r + lam) (s + mu) r s j k) = (if 1 = k then 1 else 0) :=
    fun k => linvOf_left_base_one L lam mu r s hRec h00 h11 k
  have base2 : ∀ k : ℕ, (∑ j ∈ Finset.range (2 + 1), L 2 j *
      linvOf (r + lam) (s + mu) r s j k) = (if 2 = k then 1 else 0) :=
    fun k => linvOf_left_two L hTri lam mu r s hRec h00 h11 k
  suffices hAll : ∀ n : ℕ, (∀ k : ℕ, (∑ j ∈ Finset.range (n + 1), L n j *
      linvOf (r + lam) (s + mu) r s j k) = (if n = k then 1 else 0)) ∧
      (∀ k : ℕ, (∑ j ∈ Finset.range (n + 1 + 1), L (n + 1) j *
        linvOf (r + lam) (s + mu) r s j k) = (if n + 1 = k then 1 else 0)) by
    intro n k
    exact (hAll n).1 k
  intro n
  induction n with
  | zero => exact ⟨base0, base1⟩
  | succ m ih =>
    obtain ⟨ihm, ihm1⟩ := ih
    refine ⟨ihm1, ?_⟩
    cases m with
    | zero => exact base2
    | succ t =>
      intro k
      exact linvOf_left_step L hTri lam mu r s hRec (t + 1) (by omega)
        ihm ihm1 k

/-- Row-0 Stieltjes sum against `L`. -/
private theorem stieltjes_sum_zero (r₁ s₁ r s : ℝ) (L : ℕ → ℕ → ℝ)
    (N k : ℕ) (hN : 1 < N) :
    (∑ j ∈ Finset.range N, stieltjesMatrix r₁ s₁ r s 0 j * L j k) =
      r₁ * L 0 k + L 1 k := by
  have hSub : (∑ j ∈ Finset.range N,
      stieltjesMatrix r₁ s₁ r s 0 j * L j k) =
      ∑ j ∈ Finset.range 2,
        stieltjesMatrix r₁ s₁ r s 0 j * L j k := by
    apply Eq.symm
    have hss : Finset.range 2 ⊆ Finset.range N := by
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    apply Finset.sum_subset hss
    intro j _ hj
    rw [Finset.mem_range] at hj
    have hS := stieltjes_eq_zero_of_gt r₁ s₁ r s 0 j (by omega : j > 0 + 1)
    rw [hS, zero_mul]
  rw [hSub, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  rw [stieltjes_zero_zero, stieltjes_zero_one]
  ring

/-- Row-1 Stieltjes sum against `L`. -/
private theorem stieltjes_sum_one (r₁ s₁ r s : ℝ) (L : ℕ → ℕ → ℝ)
    (N k : ℕ) (hN : 2 < N) :
    (∑ j ∈ Finset.range N, stieltjesMatrix r₁ s₁ r s 1 j * L j k) =
      s₁ * L 0 k + r * L 1 k + L 2 k := by
  have hSub : (∑ j ∈ Finset.range N,
      stieltjesMatrix r₁ s₁ r s 1 j * L j k) =
      ∑ j ∈ Finset.range 3,
        stieltjesMatrix r₁ s₁ r s 1 j * L j k := by
    apply Eq.symm
    have hss : Finset.range 3 ⊆ Finset.range N := by
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    apply Finset.sum_subset hss
    intro j _ hj
    rw [Finset.mem_range] at hj
    have hS := stieltjes_eq_zero_of_gt r₁ s₁ r s 1 j (by omega : j > 1 + 1)
    rw [hS, zero_mul]
  rw [hSub, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  rw [stieltjes_one_zero, stieltjes_one_one, stieltjes_one_two]
  ring

/-- Bulk Stieltjes sum against `L`. -/
private theorem stieltjes_sum_ge_two (r₁ s₁ r s : ℝ) (L : ℕ → ℕ → ℝ)
    (t N k : ℕ) (ht : 2 ≤ t) (hN : t + 1 < N) :
    (∑ j ∈ Finset.range N, stieltjesMatrix r₁ s₁ r s t j * L j k) =
      s * L (t - 1) k + r * L t k + L (t + 1) k := by
  have hPt : ∀ j ∈ Finset.range N, stieltjesMatrix r₁ s₁ r s t j * L j k =
      (if j = t - 1 then s * L (t - 1) k else 0) +
      (if j = t then r * L t k else 0) +
      (if j = t + 1 then L (t + 1) k else 0) := by
    intro j _
    have hS := stieltjes_ge_two r₁ s₁ r s t j ht
    by_cases hj1 : j = t + 1
    · have hj0 : ¬ j = t - 1 := by omega
      have hj2 : ¬ j = t := by omega
      rw [ite_eq_right hj0, ite_eq_right hj2, ite_eq_left hj1]
      rw [hS, ite_eq_left hj1, one_mul, hj1]
      ring
    · by_cases hj2 : j = t
      · have hj0 : ¬ j = t - 1 := by omega
        rw [ite_eq_right hj0, ite_eq_left hj2, ite_eq_right hj1]
        rw [hS, ite_eq_right hj1, ite_eq_left hj2]
        rw [hj2]
        ring
      · by_cases hj0 : j = t - 1
        · have hj1' : j + 1 = t := by omega
          rw [ite_eq_left hj0, ite_eq_right hj2, ite_eq_right hj1]
          rw [hS, ite_eq_right hj1, ite_eq_right hj2, ite_eq_left hj1']
          rw [hj0]
          ring
        · rw [ite_eq_right hj0, ite_eq_right hj2, ite_eq_right hj1]
          rw [hS, ite_eq_right hj1, ite_eq_right hj2,
            ite_eq_right (by omega : ¬ j + 1 = t)]
          rw [zero_mul]
          ring
  rw [Finset.sum_congr rfl hPt, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq']
  have m1 : t - 1 ∈ Finset.range N := by
    rw [Finset.mem_range]; omega
  have m2 : t ∈ Finset.range N := by
    rw [Finset.mem_range]; omega
  have m3 : t + 1 ∈ Finset.range N := by
    rw [Finset.mem_range]; omega
  rw [ite_eq_left m1, ite_eq_left m2, ite_eq_left m3]

/-- A Stieltjes row sum is unchanged past its superdiagonal. -/
private theorem rco_stieltjes_sum_extend (r₁ s₁ r s : ℝ) (L : ℕ → ℕ → ℝ)
    (t N k : ℕ) (hN : t + 1 < N) :
    (∑ j ∈ Finset.range N, stieltjesMatrix r₁ s₁ r s t j * L j k) =
      ∑ j ∈ Finset.range (t + 2), stieltjesMatrix r₁ s₁ r s t j * L j k := by
  apply Eq.symm
  apply Finset.sum_subset
  · intro j hj
    rw [Finset.mem_range] at hj ⊢
    omega
  · intro j _ hj
    rw [Finset.mem_range] at hj
    push Not at hj
    have hS := stieltjes_eq_zero_of_gt r₁ s₁ r s t j (by omega)
    rw [hS, zero_mul]

/-- The coefficient recurrence makes the Stieltjes matrix shift the rows of `L`. -/
private theorem rco_stieltjes_mul_L_of_recurrence (L : ℕ → ℕ → ℝ)
    (hTri : ∀ n k : ℕ, n < k → L n k = 0)
    (lam mu r s : ℝ)
    (hRec : ∀ N K : ℕ,
      L N K + r * (if 1 ≤ N then L (N - 1) K else 0) -
          (if 1 ≤ N ∧ 1 ≤ K then L (N - 1) (K - 1) else 0) +
          s * (if 2 ≤ N then L (N - 2) K else 0) =
        (if K = 0 then
          if N = 0 then 1 else if N = 1 then -lam else if N = 2 then -mu else 0
        else 0)) :
    ∀ t k : ℕ,
      (∑ j ∈ Finset.range (t + 2),
        stieltjesMatrix (r + lam) (s + mu) r s t j * L j k) =
        (if k = 0 then 0 else L t (k - 1)) := by
  have h00 : L 0 0 = 1 := recurrence_L00 L lam mu r s hRec
  intro t k
  cases t with
  | zero =>
    rw [stieltjes_sum_zero (r + lam) (s + mu) r s L 2 k (by omega)]
    cases k with
    | zero =>
      have hR := hRec 1 0
      rw [ite_eq_left (by omega : 1 ≤ (1 : ℕ)),
        ite_eq_right (by omega : ¬ (1 ≤ (1 : ℕ) ∧ 1 ≤ 0)),
        ite_eq_right (by omega : ¬ 2 ≤ (1 : ℕ)), ite_eq_left rfl,
        ite_eq_right (by omega : ¬ (1 : ℕ) = 0), ite_eq_left rfl] at hR
      have e : (1 : ℕ) - 1 = 0 := by omega
      rw [e, h00] at hR
      rw [ite_eq_left rfl, h00]
      linarith
    | succ q =>
      have hR := hRec 1 (q + 1)
      rw [ite_eq_left (by omega : 1 ≤ (1 : ℕ)),
        ite_eq_left ⟨by omega, by omega⟩,
        ite_eq_right (by omega : ¬ 2 ≤ (1 : ℕ)),
        ite_eq_right (by omega : ¬ q + 1 = 0)] at hR
      have h0 : L 0 (q + 1) = 0 := hTri 0 (q + 1) (by omega)
      rw [ite_eq_right (by omega : ¬ q + 1 = 0), h0]
      rw [h0] at hR
      linarith
  | succ n =>
    cases n with
    | zero =>
      rw [stieltjes_sum_one (r + lam) (s + mu) r s L 3 k (by omega)]
      cases k with
      | zero =>
        have hR := hRec 2 0
        rw [ite_eq_left (by omega : 1 ≤ (2 : ℕ)),
          ite_eq_right (by omega : ¬ (1 ≤ (2 : ℕ) ∧ 1 ≤ 0)),
          ite_eq_left (by omega : 2 ≤ (2 : ℕ)), ite_eq_left rfl,
          ite_eq_right (by omega : ¬ (2 : ℕ) = 0),
          ite_eq_right (by omega : ¬ (2 : ℕ) = 1), ite_eq_left rfl] at hR
        have e1 : (2 : ℕ) - 1 = 1 := by omega
        have e2 : (2 : ℕ) - 2 = 0 := by omega
        rw [e1, e2, h00] at hR
        rw [ite_eq_left rfl, h00]
        linarith
      | succ q =>
        have hR := hRec 2 (q + 1)
        rw [ite_eq_left (by omega : 1 ≤ (2 : ℕ)),
          ite_eq_left ⟨by omega, by omega⟩,
          ite_eq_left (by omega : 2 ≤ (2 : ℕ)),
          ite_eq_right (by omega : ¬ q + 1 = 0)] at hR
        have h0 : L 0 (q + 1) = 0 := hTri 0 (q + 1) (by omega)
        rw [ite_eq_right (by omega : ¬ q + 1 = 0), h0]
        rw [h0] at hR
        linarith
    | succ u =>
      have ht : u + 1 + 1 = u + 2 := by omega
      rw [ht]
      rw [stieltjes_sum_ge_two (r + lam) (s + mu) r s L (u + 2)
        (u + 2 + 2) k (by omega) (by omega)]
      cases k with
      | zero =>
        have hR := hRec (u + 3) 0
        rw [ite_eq_left (by omega : 1 ≤ u + 3),
          ite_eq_right (by omega : ¬ (1 ≤ u + 3 ∧ 1 ≤ 0)),
          ite_eq_left (by omega : 2 ≤ u + 3), ite_eq_left rfl,
          ite_eq_right (by omega : ¬ u + 3 = 0),
          ite_eq_right (by omega : ¬ u + 3 = 1),
          ite_eq_right (by omega : ¬ u + 3 = 2)] at hR
        have e1 : u + 3 - 1 = u + 2 := by omega
        have e2 : u + 3 - 2 = u + 2 - 1 := by omega
        rw [e1, e2] at hR
        rw [ite_eq_left rfl]
        linarith
      | succ q =>
        have hR := hRec (u + 3) (q + 1)
        rw [ite_eq_left (by omega : 1 ≤ u + 3),
          ite_eq_left ⟨by omega, by omega⟩,
          ite_eq_left (by omega : 2 ≤ u + 3),
          ite_eq_right (by omega : ¬ q + 1 = 0)] at hR
        have e1 : u + 3 - 1 = u + 2 := by omega
        have e2 : u + 3 - 2 = u + 2 - 1 := by omega
        rw [e1, e2] at hR
        rw [ite_eq_right (by omega : ¬ q + 1 = 0)]
        linarith

/-- The production-defined left inverse is also a right inverse. -/
private theorem rco_linvOf_right_all (L : ℕ → ℕ → ℝ)
    (hTri : ∀ n k : ℕ, n < k → L n k = 0)
    (lam mu r s : ℝ)
    (hRec : ∀ N K : ℕ,
      L N K + r * (if 1 ≤ N then L (N - 1) K else 0) -
          (if 1 ≤ N ∧ 1 ≤ K then L (N - 1) (K - 1) else 0) +
          s * (if 2 ≤ N then L (N - 2) K else 0) =
        (if K = 0 then
          if N = 0 then 1 else if N = 1 then -lam else if N = 2 then -mu else 0
        else 0)) :
    ∀ n k : ℕ, (∑ j ∈ Finset.range (n + 1),
      linvOf (r + lam) (s + mu) r s n j * L j k) =
      (if n = k then 1 else 0) := by
  have h00 : L 0 0 = 1 := recurrence_L00 L lam mu r s hRec
  have hTriM := linvOf_triangular (r + lam) (s + mu) r s
  intro n
  induction n with
  | zero =>
    intro k
    rw [Finset.sum_range_one]
    change (if (0 : ℕ) = 0 then (1 : ℝ) else 0) * L 0 k =
      (if 0 = k then 1 else 0)
    rw [ite_eq_left rfl, one_mul]
    cases k with
    | zero => rw [h00, ite_eq_left rfl]
    | succ q =>
      rw [hTri 0 (q + 1) (by omega), ite_eq_right (by omega : ¬ 0 = q + 1)]
  | succ m ih =>
    intro k
    have hExpand : (∑ j ∈ Finset.range (m + 1 + 1),
        linvOf (r + lam) (s + mu) r s (m + 1) j * L j k) =
        ∑ t ∈ Finset.range (m + 2), linvOf (r + lam) (s + mu) r s m t *
          (∑ j ∈ Finset.range (m + 2),
            stieltjesMatrix (r + lam) (s + mu) r s t j * L j k) := by
      have hDef : ∀ j : ℕ, linvOf (r + lam) (s + mu) r s (m + 1) j =
          ∑ t ∈ Finset.range (m + 2), linvOf (r + lam) (s + mu) r s m t *
            stieltjesMatrix (r + lam) (s + mu) r s t j := fun j => rfl
      rw [show m + 1 + 1 = m + 2 by omega]
      calc
        (∑ j ∈ Finset.range (m + 2),
            linvOf (r + lam) (s + mu) r s (m + 1) j * L j k) =
            ∑ j ∈ Finset.range (m + 2), ∑ t ∈ Finset.range (m + 2),
              (linvOf (r + lam) (s + mu) r s m t *
                stieltjesMatrix (r + lam) (s + mu) r s t j) * L j k := by
              apply Finset.sum_congr rfl
              intro j _
              rw [hDef j, Finset.sum_mul]
          _ = ∑ t ∈ Finset.range (m + 2), ∑ j ∈ Finset.range (m + 2),
              (linvOf (r + lam) (s + mu) r s m t *
                stieltjesMatrix (r + lam) (s + mu) r s t j) * L j k := by
              rw [Finset.sum_comm]
          _ = ∑ t ∈ Finset.range (m + 2), linvOf (r + lam) (s + mu) r s m t *
              (∑ j ∈ Finset.range (m + 2),
                stieltjesMatrix (r + lam) (s + mu) r s t j * L j k) := by
              apply Finset.sum_congr rfl
              intro t _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
    rw [hExpand, Finset.sum_range_succ]
    have hTop : linvOf (r + lam) (s + mu) r s m (m + 1) = 0 :=
      hTriM m (m + 1) (by omega)
    rw [hTop, zero_mul, add_zero]
    have hShift : ∀ t ∈ Finset.range (m + 1),
        (∑ j ∈ Finset.range (m + 2),
          stieltjesMatrix (r + lam) (s + mu) r s t j * L j k) =
          (if k = 0 then 0 else L t (k - 1)) := by
      intro t ht
      rw [Finset.mem_range] at ht
      rw [rco_stieltjes_sum_extend (r + lam) (s + mu) r s L t (m + 2) k (by omega)]
      exact rco_stieltjes_mul_L_of_recurrence L hTri lam mu r s hRec t k
    rw [Finset.sum_congr rfl (fun t ht => by rw [hShift t ht])]
    cases k with
    | zero =>
      rw [Finset.sum_congr rfl (fun _ _ => by rw [ite_eq_left rfl, mul_zero]),
        Finset.sum_const_zero, ite_eq_right (by omega : ¬ m + 1 = 0)]
    | succ q =>
      have hk : ¬ q + 1 = 0 := by omega
      have hKm1 : q + 1 - 1 = q := by omega
      rw [Finset.sum_congr rfl (fun _ _ => by rw [ite_eq_right hk, hKm1]), ih q]
      by_cases hmq : m = q
      · rw [ite_eq_left hmq, ite_eq_left (by omega : m + 1 = q + 1)]
      · rw [ite_eq_right hmq, ite_eq_right (by omega : ¬ m + 1 = q + 1)]

/-- The coefficient recurrence supplies the required Stieltjes inverse array. -/
private theorem rco_recurrence_to_stieltjes (d h : PowerSeries ℝ) (L : ℕ → ℕ → ℝ)
    (h0 : PowerSeries.coeff 0 h = 0)
    (hL : ∀ n k : ℕ, L n k = PowerSeries.coeff n (d * h ^ k))
    (lam mu r s : ℝ) (hs : s ≠ 0) (hsm : s + mu ≠ 0)
    (hRec : ∀ N K : ℕ,
      L N K + r * (if 1 ≤ N then L (N - 1) K else 0) -
          (if 1 ≤ N ∧ 1 ≤ K then L (N - 1) (K - 1) else 0) +
          s * (if 2 ≤ N then L (N - 2) K else 0) =
        (if K = 0 then
          if N = 0 then 1 else if N = 1 then -lam else if N = 2 then -mu else 0
        else 0)) :
    ∃ Linv : ℕ → ℕ → ℝ, ∃ r₁ s₁ r' s' : ℝ,
      L 0 0 = 1 ∧ s₁ ≠ 0 ∧ s' ≠ 0 ∧
      (∀ n k : ℕ, k > n → L n k = 0) ∧
      (∀ n k : ℕ, k > n → Linv n k = 0) ∧
      (∀ n k : ℕ, (∑ j ∈ Finset.range (n + 1), L n j * Linv j k) =
        (if n = k then 1 else 0)) ∧
      (∀ n k : ℕ, (∑ j ∈ Finset.range (n + 1), Linv n j * L j k) =
        (if n = k then 1 else 0)) ∧
      (∀ n k : ℕ, Linv (n + 1) k =
        ∑ j ∈ Finset.range (n + 2), Linv n j * stieltjesMatrix r₁ s₁ r' s' j k) := by
  have hTri : ∀ n k : ℕ, k > n → L n k = 0 :=
    fun n k hk => riordan_L_triangular d h L h0 hL n k hk
  have h00 : L 0 0 = 1 := recurrence_L00 L lam mu r s hRec
  have hDiag : ∀ n : ℕ, L n n = 1 :=
    recurrence_diag_eq_one L hTri lam mu r s hRec
  refine ⟨linvOf (r + lam) (s + mu) r s, r + lam, s + mu, r, s,
    h00, hsm, hs, hTri, linvOf_triangular (r + lam) (s + mu) r s, ?_, ?_, ?_⟩
  · exact linvOf_left_all L hTri lam mu r s hRec h00 (hDiag 1)
  · exact rco_linvOf_right_all L hTri lam mu r s hRec
  · intro n k
    rfl

/-- A triangular inverse satisfying the Stieltjes production law has unit diagonal. -/
private theorem rco_inverse_diag (L Linv : ℕ → ℕ → ℝ) (r₁ s₁ r s : ℝ)
    (h00 : L 0 0 = 1)
    (hTriInv : ∀ n k : ℕ, k > n → Linv n k = 0)
    (hRight : ∀ n k : ℕ, (∑ j ∈ Finset.range (n + 1), Linv n j * L j k) =
      (if n = k then 1 else 0))
    (hProd : ∀ n k : ℕ, Linv (n + 1) k =
      ∑ j ∈ Finset.range (n + 2), Linv n j * stieltjesMatrix r₁ s₁ r s j k) :
    ∀ n : ℕ, Linv n n = 1 := by
  intro n
  induction n with
  | zero =>
    have hR := hRight 0 0
    rw [Finset.sum_range_one, h00, mul_one, ite_eq_left rfl] at hR
    exact hR
  | succ m ih =>
    rw [hProd m (m + 1), Finset.sum_eq_single m]
    · rw [ih, stieltjes_succ, one_mul]
    · intro j hj hjm
      rw [Finset.mem_range] at hj
      by_cases hjle : j ≤ m
      · have hS := stieltjes_eq_zero_of_gt r₁ s₁ r s j (m + 1) (by omega)
        rw [hS, mul_zero]
      · have hjEq : j = m + 1 := by omega
        rw [hjEq, hTriInv m (m + 1) (by omega), zero_mul]
    · intro hm
      have hmem : m ∈ Finset.range (m + 2) := by
        rw [Finset.mem_range]
        omega
      exact absurd hmem hm

/-- Expanding one production step against a column of `L` swaps two finite sums. -/
private theorem rco_production_right_expand (L Linv : ℕ → ℕ → ℝ)
    (r₁ s₁ r s : ℝ)
    (hProd : ∀ n k : ℕ, Linv (n + 1) k =
      ∑ j ∈ Finset.range (n + 2), Linv n j * stieltjesMatrix r₁ s₁ r s j k)
    (n k : ℕ) :
    (∑ i ∈ Finset.range (n + 2), Linv (n + 1) i * L i k) =
      ∑ t ∈ Finset.range (n + 2), Linv n t *
        (∑ i ∈ Finset.range (n + 2), stieltjesMatrix r₁ s₁ r s t i * L i k) := by
  calc
    (∑ i ∈ Finset.range (n + 2), Linv (n + 1) i * L i k) =
        ∑ i ∈ Finset.range (n + 2), ∑ t ∈ Finset.range (n + 2),
          (Linv n t * stieltjesMatrix r₁ s₁ r s t i) * L i k := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hProd n i, Finset.sum_mul]
    _ = ∑ t ∈ Finset.range (n + 2), ∑ i ∈ Finset.range (n + 2),
        (Linv n t * stieltjesMatrix r₁ s₁ r s t i) * L i k := by
          rw [Finset.sum_comm]
    _ = ∑ t ∈ Finset.range (n + 2), Linv n t *
        (∑ i ∈ Finset.range (n + 2),
          stieltjesMatrix r₁ s₁ r s t i * L i k) := by
          apply Finset.sum_congr rfl
          intro t _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring

/-- Two-sided inversion turns the production matrix into the row-shift operator. -/
private theorem rco_stieltjes_mul_L_of_inverse (L Linv : ℕ → ℕ → ℝ)
    (r₁ s₁ r s : ℝ)
    (h00 : L 0 0 = 1)
    (hTriInv : ∀ n k : ℕ, k > n → Linv n k = 0)
    (hRight : ∀ n k : ℕ, (∑ j ∈ Finset.range (n + 1), Linv n j * L j k) =
      (if n = k then 1 else 0))
    (hProd : ∀ n k : ℕ, Linv (n + 1) k =
      ∑ j ∈ Finset.range (n + 2), Linv n j * stieltjesMatrix r₁ s₁ r s j k) :
    ∀ n k : ℕ,
      (∑ j ∈ Finset.range (n + 2), stieltjesMatrix r₁ s₁ r s n j * L j k) =
        (if k = 0 then 0 else L n (k - 1)) := by
  have hDiag : ∀ n : ℕ, Linv n n = 1 :=
    rco_inverse_diag L Linv r₁ s₁ r s h00 hTriInv hRight hProd
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro k
    have hExpand := rco_production_right_expand L Linv r₁ s₁ r s hProd n k
    have hSum : (∑ t ∈ Finset.range (n + 2), Linv n t *
        (∑ j ∈ Finset.range (n + 2), stieltjesMatrix r₁ s₁ r s t j * L j k)) =
        (if n + 1 = k then 1 else 0) := by
      rw [← hExpand]
      exact hRight (n + 1) k
    rw [Finset.sum_range_succ] at hSum
    have hTop : Linv n (n + 1) = 0 := hTriInv n (n + 1) (by omega)
    rw [hTop, zero_mul, add_zero, Finset.sum_range_succ, hDiag n, one_mul] at hSum
    have hEarlier : ∀ t ∈ Finset.range n,
        (∑ j ∈ Finset.range (n + 2), stieltjesMatrix r₁ s₁ r s t j * L j k) =
          (if k = 0 then 0 else L t (k - 1)) := by
      intro t ht
      rw [Finset.mem_range] at ht
      rw [rco_stieltjes_sum_extend r₁ s₁ r s L t (n + 2) k (by omega)]
      exact ih t ht k
    rw [Finset.sum_congr rfl (fun t ht => by rw [hEarlier t ht])] at hSum
    cases k with
    | zero =>
      rw [Finset.sum_congr rfl (fun _ _ => by rw [ite_eq_left rfl, mul_zero]),
        Finset.sum_const_zero, zero_add,
        ite_eq_right (by omega : ¬ n + 1 = 0)] at hSum
      rw [ite_eq_left rfl]
      exact hSum
    | succ q =>
      have hk : ¬ q + 1 = 0 := by omega
      have hKm1 : q + 1 - 1 = q := by omega
      rw [Finset.sum_congr rfl (fun _ _ => by rw [ite_eq_right hk, hKm1])] at hSum
      have hIte : (if n + 1 = q + 1 then (1 : ℝ) else 0) =
          (if n = q then 1 else 0) := by
        by_cases hnq : n = q
        · rw [ite_eq_left hnq, ite_eq_left (by omega : n + 1 = q + 1)]
        · rw [ite_eq_right hnq, ite_eq_right (by omega : ¬ n + 1 = q + 1)]
      rw [hIte] at hSum
      have hPrev := hRight n q
      rw [Finset.sum_range_succ, hDiag n, one_mul] at hPrev
      rw [ite_eq_right hk, hKm1]
      linarith

/-- A Stieltjes inverse array yields the explicit coefficient recurrence. -/
private theorem rco_stieltjes_to_recurrence (L Linv : ℕ → ℕ → ℝ)
    (r₁ s₁ r s : ℝ)
    (h00 : L 0 0 = 1) (hs₁ : s₁ ≠ 0) (hs : s ≠ 0)
    (hTri : ∀ n k : ℕ, k > n → L n k = 0)
    (hTriInv : ∀ n k : ℕ, k > n → Linv n k = 0)
    (hRight : ∀ n k : ℕ, (∑ j ∈ Finset.range (n + 1), Linv n j * L j k) =
      (if n = k then 1 else 0))
    (hProd : ∀ n k : ℕ, Linv (n + 1) k =
      ∑ j ∈ Finset.range (n + 2), Linv n j * stieltjesMatrix r₁ s₁ r s j k) :
    ∃ lam mu r' s' : ℝ, s' ≠ 0 ∧ s' + mu ≠ 0 ∧
      ∀ N K : ℕ,
        L N K + r' * (if 1 ≤ N then L (N - 1) K else 0) -
            (if 1 ≤ N ∧ 1 ≤ K then L (N - 1) (K - 1) else 0) +
            s' * (if 2 ≤ N then L (N - 2) K else 0) =
          (if K = 0 then
            if N = 0 then 1 else if N = 1 then -lam else if N = 2 then -mu else 0
          else 0) := by
  have hShift := rco_stieltjes_mul_L_of_inverse L Linv r₁ s₁ r s
    h00 hTriInv hRight hProd
  refine ⟨r₁ - r, s₁ - s, r, s, hs, ?_, ?_⟩
  · rwa [show s + (s₁ - s) = s₁ by ring]
  · intro N K
    cases N with
    | zero =>
      cases K with
      | zero =>
        rw [ite_eq_right (by omega : ¬ 1 ≤ (0 : ℕ)),
          ite_eq_right (by omega : ¬ (1 ≤ (0 : ℕ) ∧ 1 ≤ 0)),
          ite_eq_right (by omega : ¬ 2 ≤ (0 : ℕ)), ite_eq_left rfl,
          ite_eq_left rfl, h00]
        ring
      | succ q =>
        rw [ite_eq_right (by omega : ¬ 1 ≤ (0 : ℕ)),
          ite_eq_right (by omega : ¬ (1 ≤ (0 : ℕ) ∧ 1 ≤ q + 1)),
          ite_eq_right (by omega : ¬ 2 ≤ (0 : ℕ)),
          ite_eq_right (by omega : ¬ q + 1 = 0),
          hTri 0 (q + 1) (by omega)]
        ring
    | succ n =>
      cases n with
      | zero =>
        have hS := hShift 0 K
        rw [stieltjes_sum_zero r₁ s₁ r s L 2 K (by omega)] at hS
        cases K with
        | zero =>
          rw [ite_eq_left rfl] at hS
          rw [ite_eq_left (by omega : 1 ≤ (1 : ℕ)),
            ite_eq_right (by omega : ¬ (1 ≤ (1 : ℕ) ∧ 1 ≤ 0)),
            ite_eq_right (by omega : ¬ 2 ≤ (1 : ℕ)), ite_eq_left rfl,
            ite_eq_right (by omega : ¬ (1 : ℕ) = 0), ite_eq_left rfl]
          have e : (1 : ℕ) - 1 = 0 := by omega
          rw [e, h00]
          rw [h00] at hS
          linarith
        | succ q =>
          have hk : ¬ q + 1 = 0 := by omega
          have hKm1 : q + 1 - 1 = q := by omega
          rw [ite_eq_right hk, hKm1] at hS
          have h0 : L 0 (q + 1) = 0 := hTri 0 (q + 1) (by omega)
          rw [ite_eq_left (by omega : 1 ≤ (1 : ℕ)),
            ite_eq_left ⟨by omega, by omega⟩,
            ite_eq_right (by omega : ¬ 2 ≤ (1 : ℕ)), ite_eq_right hk]
          rw [h0] at hS
          rw [show (0 : ℕ) + 1 = 1 by omega,
            show (0 : ℕ) + 1 - 1 = 0 by omega, hKm1, h0]
          linarith
      | succ m =>
        cases m with
        | zero =>
          have hS := hShift 1 K
          rw [stieltjes_sum_one r₁ s₁ r s L 3 K (by omega)] at hS
          cases K with
          | zero =>
            rw [ite_eq_left rfl] at hS
            rw [ite_eq_left (by omega : 1 ≤ (2 : ℕ)),
              ite_eq_right (by omega : ¬ (1 ≤ (2 : ℕ) ∧ 1 ≤ 0)),
              ite_eq_left (by omega : 2 ≤ (2 : ℕ)), ite_eq_left rfl,
              ite_eq_right (by omega : ¬ (2 : ℕ) = 0),
              ite_eq_right (by omega : ¬ (2 : ℕ) = 1), ite_eq_left rfl]
            rw [show (2 : ℕ) - 1 = 1 by omega, show (2 : ℕ) - 2 = 0 by omega, h00]
            rw [h00] at hS
            linarith
          | succ q =>
            have hk : ¬ q + 1 = 0 := by omega
            have hKm1 : q + 1 - 1 = q := by omega
            rw [ite_eq_right hk, hKm1] at hS
            have h0 : L 0 (q + 1) = 0 := hTri 0 (q + 1) (by omega)
            rw [ite_eq_left (by omega : 1 ≤ (2 : ℕ)),
              ite_eq_left ⟨by omega, by omega⟩,
              ite_eq_left (by omega : 2 ≤ (2 : ℕ)), ite_eq_right hk]
            rw [h0] at hS
            rw [show (0 : ℕ) + 1 + 1 = 2 by omega,
              show (2 : ℕ) - 1 = 1 by omega, show (2 : ℕ) - 2 = 0 by omega,
              hKm1, h0]
            linarith
        | succ u =>
          have hS := hShift (u + 2) K
          rw [stieltjes_sum_ge_two r₁ s₁ r s L (u + 2) (u + 2 + 2) K
            (by omega) (by omega)] at hS
          cases K with
          | zero =>
            rw [ite_eq_left rfl] at hS
            rw [ite_eq_left (by omega : 1 ≤ u + 3),
              ite_eq_right (by omega : ¬ (1 ≤ u + 3 ∧ 1 ≤ 0)),
              ite_eq_left (by omega : 2 ≤ u + 3), ite_eq_left rfl,
              ite_eq_right (by omega : ¬ u + 3 = 0),
              ite_eq_right (by omega : ¬ u + 3 = 1),
              ite_eq_right (by omega : ¬ u + 3 = 2)]
            rw [show u + 3 - 1 = u + 2 by omega,
              show u + 3 - 2 = u + 2 - 1 by omega]
            linarith
          | succ q =>
            have hk : ¬ q + 1 = 0 := by omega
            have hKm1 : q + 1 - 1 = q := by omega
            rw [ite_eq_right hk, hKm1] at hS
            rw [ite_eq_left (by omega : 1 ≤ u + 3),
              ite_eq_left ⟨by omega, by omega⟩,
              ite_eq_left (by omega : 2 ≤ u + 3), ite_eq_right hk]
            rw [show u + 3 - 1 = u + 2 by omega,
              show u + 3 - 2 = u + 2 - 1 by omega, hKm1]
            linarith

/-- Monic orthogonality is equivalent to the explicit coefficient recurrence. -/
private theorem rco_orthogonal_iff_recurrence (d h : PowerSeries ℝ)
    (L : ℕ → ℕ → ℝ) (h0 : PowerSeries.coeff 0 h = 0)
    (hL : ∀ n k : ℕ, L n k = PowerSeries.coeff n (d * h ^ k)) :
    (∃ P : ℕ → Polynomial ℝ,
        (∀ n k : ℕ, Polynomial.coeff (P n) k = L n k) ∧
        (∀ n : ℕ, (P n).Monic) ∧ Polynomial.IsFormallyOrthogonal P) ↔
      ∃ lam mu r s : ℝ, s ≠ 0 ∧ s + mu ≠ 0 ∧
        ∀ N K : ℕ,
          L N K + r * (if 1 ≤ N then L (N - 1) K else 0) -
              (if 1 ≤ N ∧ 1 ≤ K then L (N - 1) (K - 1) else 0) +
              s * (if 2 ≤ N then L (N - 2) K else 0) =
            (if K = 0 then
              if N = 0 then 1 else if N = 1 then -lam else if N = 2 then -mu else 0
            else 0) := by
  constructor
  · rintro ⟨P, hPL, hmonic, horth⟩
    exact orthogonal_to_recurrence d h L h0 hL P hPL hmonic horth
  · rintro ⟨lam, mu, r, s, hs, hsm, hRec⟩
    exact recurrence_to_orthogonal d h L h0 hL lam mu r s hs hsm hRec

/-- The Meixner power-series form is equivalent to the coefficient recurrence. -/
private theorem rco_meixner_iff_recurrence (d h : PowerSeries ℝ)
    (L : ℕ → ℕ → ℝ) (hd0 : PowerSeries.coeff 0 d ≠ 0)
    (hL : ∀ n k : ℕ, L n k = PowerSeries.coeff n (d * h ^ k)) :
    (∃ lam mu r s : ℝ, s ≠ 0 ∧ s + mu ≠ 0 ∧
        d * (1 + PowerSeries.C r * PowerSeries.X +
            PowerSeries.C s * PowerSeries.X ^ 2) =
          1 - PowerSeries.C lam * PowerSeries.X -
            PowerSeries.C mu * PowerSeries.X ^ 2 ∧
        h * (1 + PowerSeries.C r * PowerSeries.X +
            PowerSeries.C s * PowerSeries.X ^ 2) = PowerSeries.X) ↔
      ∃ lam mu r s : ℝ, s ≠ 0 ∧ s + mu ≠ 0 ∧
        ∀ N K : ℕ,
          L N K + r * (if 1 ≤ N then L (N - 1) K else 0) -
              (if 1 ≤ N ∧ 1 ≤ K then L (N - 1) (K - 1) else 0) +
              s * (if 2 ≤ N then L (N - 2) K else 0) =
            (if K = 0 then
              if N = 0 then 1 else if N = 1 then -lam else if N = 2 then -mu else 0
            else 0) := by
  constructor
  · rintro ⟨lam, mu, r, s, hs, hsm, hd, hh⟩
    exact ⟨lam, mu, r, s, hs, hsm, meixner_to_recurrence d h L hL lam mu r s hd hh⟩
  · rintro ⟨lam, mu, r, s, hs, hsm, hRec⟩
    obtain ⟨hd, hh⟩ := recurrence_to_meixner d h L hL hd0 lam mu r s hRec
    exact ⟨lam, mu, r, s, hs, hsm, hd, hh⟩

/-- The Stieltjes inverse form is equivalent to the coefficient recurrence. -/
private theorem rco_stieltjes_iff_recurrence (d h : PowerSeries ℝ)
    (L : ℕ → ℕ → ℝ) (h0 : PowerSeries.coeff 0 h = 0)
    (hL : ∀ n k : ℕ, L n k = PowerSeries.coeff n (d * h ^ k)) :
    (∃ Linv : ℕ → ℕ → ℝ, ∃ r₁ s₁ r s : ℝ, L 0 0 = 1 ∧ s₁ ≠ 0 ∧ s ≠ 0 ∧
        (∀ n k : ℕ, k > n → L n k = 0) ∧
        (∀ n k : ℕ, k > n → Linv n k = 0) ∧
        (∀ n k : ℕ, (∑ j ∈ Finset.range (n + 1), L n j * Linv j k) =
          (if n = k then 1 else 0)) ∧
        (∀ n k : ℕ, (∑ j ∈ Finset.range (n + 1), Linv n j * L j k) =
          (if n = k then 1 else 0)) ∧
        (∀ n k : ℕ, Linv (n + 1) k =
          ∑ j ∈ Finset.range (n + 2), Linv n j * stieltjesMatrix r₁ s₁ r s j k)) ↔
      ∃ lam mu r s : ℝ, s ≠ 0 ∧ s + mu ≠ 0 ∧
        ∀ N K : ℕ,
          L N K + r * (if 1 ≤ N then L (N - 1) K else 0) -
              (if 1 ≤ N ∧ 1 ≤ K then L (N - 1) (K - 1) else 0) +
              s * (if 2 ≤ N then L (N - 2) K else 0) =
            (if K = 0 then
              if N = 0 then 1 else if N = 1 then -lam else if N = 2 then -mu else 0
            else 0) := by
  constructor
  · rintro ⟨Linv, r₁, s₁, r, s, h00, hs₁, hs, hTri, hTriInv,
      _hLeft, hRight, hProd⟩
    exact rco_stieltjes_to_recurrence L Linv r₁ s₁ r s h00 hs₁ hs hTri hTriInv
      hRight hProd
  · rintro ⟨lam, mu, r, s, hs, hsm, hRec⟩
    exact rco_recurrence_to_stieltjes d h L h0 hL lam mu r s hs hsm hRec

/--
Riordan characterization of coefficient arrays of monic orthogonal polynomials:
for a Riordan array `L = (d, h)`, being the coefficient array of a family of
monic orthogonal polynomials is equivalent to each of: the Meixner-type
`(d, h)`-form with nonzero recurrence subdiagonal; the Stieltjes
production-matrix form of the inverse array with the monic normalization
`L 0 0 = 1`; and the coefficient recurrence form with the same nondegeneracy
condition.

Source: Paul Barry and Aoife Hennessy, "Meixner-Type Results for Riordan Arrays
and Associated Integer Sequences," Journal of Integer Sequences 13 (2010),
Article 10.9.4, Proposition (referee's summary of the main results),
lines 733–752,
https://cs.uwaterloo.ca/journals/JIS/VOL13/Barry5/barry96s.tex

Proves `Wanted` entry `riordan_coeff_orth_equiv`.

Proof: The coefficient recurrence is the common hub. The Meixner equivalence follows from
Barry-Hennessy, the orthogonality equivalence from Favard's theorem as in Chihara, and the
inverse-array equivalence from the `linvOf` Stieltjes production construction.
-/
public theorem riordan_coeff_orth_equiv :
    ∀ (d h : PowerSeries ℝ) (L : ℕ → ℕ → ℝ),
      (PowerSeries.coeff 0 h = 0 ∧ PowerSeries.coeff 1 h ≠ 0 ∧
        PowerSeries.coeff 0 d ≠ 0 ∧
        ∀ n k : ℕ, L n k = PowerSeries.coeff n (d * h ^ k)) →
      let IsMonicOrthogonalCoeffArray :=
        ∃ P : ℕ → Polynomial ℝ,
          (∀ n k : ℕ, Polynomial.coeff (P n) k = L n k) ∧
          (∀ n : ℕ, (P n).Monic) ∧ Polynomial.IsFormallyOrthogonal P
      (IsMonicOrthogonalCoeffArray ↔
          ∃ lam mu r s : ℝ, s ≠ 0 ∧ s + mu ≠ 0 ∧
            d * (1 + PowerSeries.C r * (PowerSeries.X : PowerSeries ℝ) +
                PowerSeries.C s * (PowerSeries.X : PowerSeries ℝ) ^ 2) =
              1 - PowerSeries.C lam * (PowerSeries.X : PowerSeries ℝ) -
                PowerSeries.C mu * (PowerSeries.X : PowerSeries ℝ) ^ 2 ∧
            h * (1 + PowerSeries.C r * (PowerSeries.X : PowerSeries ℝ) +
                PowerSeries.C s * (PowerSeries.X : PowerSeries ℝ) ^ 2) =
              (PowerSeries.X : PowerSeries ℝ)) ∧
        (IsMonicOrthogonalCoeffArray ↔
          ∃ Linv : ℕ → ℕ → ℝ, ∃ r₁ s₁ r s : ℝ, L 0 0 = 1 ∧ s₁ ≠ 0 ∧ s ≠ 0 ∧
            (∀ n k : ℕ, k > n → L n k = 0) ∧
            (∀ n k : ℕ, k > n → Linv n k = 0) ∧
            (∀ n k : ℕ, (∑ j ∈ Finset.range (n + 1), L n j * Linv j k) =
              (if n = k then 1 else 0)) ∧
            (∀ n k : ℕ, (∑ j ∈ Finset.range (n + 1), Linv n j * L j k) =
              (if n = k then 1 else 0)) ∧
            (∀ n k : ℕ, Linv (n + 1) k =
              ∑ j ∈ Finset.range (n + 2), Linv n j * stieltjesMatrix r₁ s₁ r s j k)) ∧
        (IsMonicOrthogonalCoeffArray ↔
          ∃ lam mu r s : ℝ, s ≠ 0 ∧ s + mu ≠ 0 ∧
            ∀ N K : ℕ,
              L N K + r * (if 1 ≤ N then L (N - 1) K else 0) -
                  (if 1 ≤ N ∧ 1 ≤ K then L (N - 1) (K - 1) else 0) +
                  s * (if 2 ≤ N then L (N - 2) K else 0) =
                (if K = 0 then
                  if N = 0 then 1 else if N = 1 then -lam else if N = 2 then -mu else 0
                else 0)) := by
  intro d h L hRiordan
  obtain ⟨h0, _h1, hd0, hL⟩ := hRiordan
  dsimp only
  have hOrthRec := rco_orthogonal_iff_recurrence d h L h0 hL
  have hMeixRec := rco_meixner_iff_recurrence d h L hd0 hL
  have hStieltjesRec := rco_stieltjes_iff_recurrence d h L h0 hL
  exact ⟨hOrthRec.trans hMeixRec.symm, hOrthRec.trans hStieltjesRec.symm, hOrthRec⟩

end MetaMathlibExt
end
