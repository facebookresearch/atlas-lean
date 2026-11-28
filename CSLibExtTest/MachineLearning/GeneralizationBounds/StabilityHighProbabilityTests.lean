/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.GeneralizationBounds.StabilityHighProbability
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Tests for the `κ / m` deletion-stability corollary

Closed instantiations of `IsDeletionStable.one_sub_le_measureReal_risk_le_div` (the `β = κ / m`
corollary of Bousquet–Elisseeff Theorem 12): a constant family, the Bool empirical-mean family
with its numeric instance, and the degenerate zero loss, plus an axiom audit.
-/

open MeasureTheory Real
open CSLibExt.MachineLearning.GeneralizationBounds

namespace CSLibExtTest.StabilityHighProbability

-- T1: constant size-indexed family with `κ = 0`; only the `M` correction remains.
private noncomputable def constLoss : Unit → Unit → ℝ := fun _ _ => 1 / 2

private def constFam (k : ℕ) (_ : Fin k → Unit) : Unit := ()

example (ν : Measure Unit) [IsProbabilityMeasure ν] (n : ℕ) {δ : ℝ}
    (hδ : δ ∈ Set.Ioo 0 1) :
    1 - δ ≤ (Measure.pi fun _ : Fin (n + 1) => ν).real
      {S | risk constLoss ν (constFam (n + 1) S) ≤
        empiricalRisk constLoss S (constFam (n + 1) S) +
        √(log (1 / δ) / (2 * ((n : ℝ) + 1)))} := by
  have hmeas : Measurable fun p : (Fin (n + 1) → Unit) × Unit =>
      constLoss (constFam (n + 1) p.1) p.2 := measurable_of_finite _
  have hmeas' : Measurable fun p : (Fin n → Unit) × Unit =>
      constLoss (constFam n p.1) p.2 := measurable_of_finite _
  have hbdd : ∀ S z, constLoss (constFam (n + 1) S) z ∈ Set.Icc 0 1 :=
    fun S z => Set.mem_Icc.mpr ⟨by norm_num [constLoss], by norm_num [constLoss]⟩
  have hbdd' : ∀ S z, constLoss (constFam n S) z ∈ Set.Icc 0 1 :=
    fun S z => Set.mem_Icc.mpr ⟨by norm_num [constLoss], by norm_num [constLoss]⟩
  have hstab : IsDeletionStable constLoss (constFam (n + 1)) (constFam n)
      (0 / ((n : ℝ) + 1)) := by
    intro S i z
    simp [constLoss]
  have h := IsDeletionStable.one_sub_le_measureReal_risk_le_div (ν := ν) hmeas
    hmeas' hbdd hbdd' hstab hδ
  simpa using h

-- T2: empirical-mean family on `Bool` with truncated absolute loss.
private def bit (b : Bool) : ℝ := if b then 1 else 0

private noncomputable def meanFit (k : ℕ) (S : Fin k → Bool) : ℝ :=
  (1 / (k : ℝ)) * ∑ i, bit (S i)

private noncomputable def truncLoss (h : ℝ) (b : Bool) : ℝ :=
  min 1 ‖h - bit b‖

private theorem lipschitz_truncLoss (c a b : ℝ) :
    |min 1 ‖a - c‖ - min 1 ‖b - c‖| ≤ |a - b| := by
  have hmin : ∀ x y : ℝ, |min (1 : ℝ) x - min 1 y| ≤ |x - y| := by
    intro x y
    rcases le_total x 1 with hx | hx <;> rcases le_total y 1 with hy | hy
    · rw [min_eq_right hx, min_eq_right hy]
    · rw [min_eq_right hx, min_eq_left hy,
        abs_of_nonpos (show x - 1 ≤ 0 by linarith),
        abs_of_nonpos (show x - y ≤ 0 by linarith)]
      linarith
    · rw [min_eq_left hx, min_eq_right hy,
        abs_of_nonneg (show (0 : ℝ) ≤ 1 - y by linarith),
        abs_of_nonneg (show (0 : ℝ) ≤ x - y by linarith)]
      linarith
    · rw [min_eq_left hx, min_eq_left hy, sub_self, abs_zero]
      exact abs_nonneg _
  have hnorm : |‖a - c‖ - ‖b - c‖| ≤ |a - b| := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have h := abs_abs_sub_abs_le_abs_sub (a - c) (b - c)
    rwa [show (a - c) - (b - c) = a - b from by ring] at h
  exact (hmin _ _).trans hnorm

private theorem stableMean (n : ℕ) :
    IsDeletionStable truncLoss (meanFit (n + 1)) (meanFit n)
      (1 / ((n : ℝ) + 1)) := by
  have hb0 : ∀ b : Bool, 0 ≤ bit b := fun b => by cases b <;> norm_num [bit]
  have hb1 : ∀ b : Bool, bit b ≤ 1 := fun b => by cases b <;> norm_num [bit]
  intro S i z
  have hlip : |truncLoss (meanFit (n + 1) S) z -
      truncLoss (meanFit n (i.removeNth S)) z| ≤
      |meanFit (n + 1) S - meanFit n (i.removeNth S)| := by
    have h := lipschitz_truncLoss (bit z) (meanFit (n + 1) S)
      (meanFit n (i.removeNth S))
    simpa [truncLoss] using h
  refine hlip.trans ?_
  have hsum : ∑ j, bit (S j) =
      bit (S i) + ∑ j, bit ((i.removeNth S) j) := by
    exact Fin.sum_univ_succAbove _ i
  have hT0 : 0 ≤ ∑ j, bit ((i.removeNth S) j) :=
    Finset.sum_nonneg fun j _ => hb0 _
  have hTn : ∑ j, bit ((i.removeNth S) j) ≤ (n : ℝ) := by
    calc ∑ j, bit ((i.removeNth S) j) ≤ ∑ _j : Fin n, 1 :=
          Finset.sum_le_sum fun j _ => hb1 _
      _ = (n : ℝ) := by simp
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_cast
  have hfull : meanFit (n + 1) S =
      (bit (S i) + ∑ j, bit ((i.removeNth S) j)) / ((n : ℝ) + 1) := by
    simp only [meanFit, hsum, hcast]
    ring
  have hshort : meanFit n (i.removeNth S) =
      (∑ j, bit ((i.removeNth S) j)) / (n : ℝ) := by
    simp only [meanFit]
    ring
  have hx01 : bit (S i) = 0 ∨ bit (S i) = 1 := by
    cases S i <;> simp [bit]
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · have h0 : meanFit 0 (i.removeNth S) = 0 := by simp [meanFit]
    have hempty : ∑ j : Fin 0, bit ((i.removeNth S) j) = 0 := by simp
    rw [hfull, h0, hempty]
    rcases hx01 with hx | hx <;> rw [hx] <;> norm_num
  · have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hnpos.ne'
    have hm0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hm0' : ((n : ℝ) + 1) ≠ 0 := hm0.ne'
    have hid : (bit (S i) + ∑ j, bit ((i.removeNth S) j)) / ((n : ℝ) + 1) -
        (∑ j, bit ((i.removeNth S) j)) / (n : ℝ) =
        ((n : ℝ) * bit (S i) - ∑ j, bit ((i.removeNth S) j)) /
          ((n : ℝ) * ((n : ℝ) + 1)) := by
      field_simp
      ring
    have hnum : |(n : ℝ) * bit (S i) - ∑ j, bit ((i.removeNth S) j)| ≤ n := by
      rcases hx01 with hx | hx
      · rw [hx, mul_zero, zero_sub, abs_neg, abs_of_nonneg hT0]
        exact hTn
      · rw [hx, mul_one, abs_of_nonneg (sub_nonneg.mpr hTn)]
        linarith [hT0]
    have hden0 : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) :=
      mul_pos (by exact_mod_cast hnpos) hm0
    rw [hfull, hshort, hid, abs_div, abs_of_pos hden0,
      div_le_div_iff₀ hden0 hm0, one_mul]
    exact mul_le_mul_of_nonneg_right hnum hm0.le

private theorem measMean (k : ℕ) :
    Measurable fun p : (Fin k → Bool) × Bool =>
      truncLoss (meanFit k p.1) p.2 :=
  measurable_of_finite _

private theorem bddTrunc (k : ℕ) (S : Fin k → Bool) (b : Bool) :
    truncLoss (meanFit k S) b ∈ Set.Icc 0 1 :=
  ⟨le_min zero_le_one (norm_nonneg _), min_le_left 1 _⟩

example (ν : Measure Bool) [IsProbabilityMeasure ν] (n : ℕ) {δ : ℝ}
    (hδ : δ ∈ Set.Ioo 0 1) :
    1 - δ ≤ (Measure.pi fun _ : Fin (n + 1) => ν).real
      {S | risk truncLoss ν (meanFit (n + 1) S) ≤
        empiricalRisk truncLoss S (meanFit (n + 1) S) +
        2 * 1 / ((n : ℝ) + 1) +
        (4 * 1 + 1) * √(log (1 / δ) / (2 * ((n : ℝ) + 1)))} :=
  IsDeletionStable.one_sub_le_measureReal_risk_le_div (ν := ν) (measMean (n + 1))
    (measMean n) (bddTrunc (n + 1)) (bddTrunc n) (stableMean n) hδ

-- T2 numeric: `n = 199`, `δ = 1 / 20`, uniform law on `Bool`.
private noncomputable def boolUniform : Measure Bool :=
  (1 / 2 : ENNReal) • (Measure.dirac false + Measure.dirac true)

private theorem boolUniform_univ : boolUniform Set.univ = 1 := by
  simp only [boolUniform, smul_apply, add_apply, smul_eq_mul,
    Measure.dirac_apply_of_mem (Set.mem_univ false),
    Measure.dirac_apply_of_mem (Set.mem_univ true)]
  norm_num
  exact ENNReal.inv_mul_cancel (by simp) (by simp)

private theorem boolUniform_true : boolUniform {true} = 1 / 2 := by
  simp [boolUniform, smul_apply, add_apply, smul_eq_mul]

private theorem boolUniform_false : boolUniform {false} = 1 / 2 := by
  simp [boolUniform, smul_apply, add_apply, smul_eq_mul]

private instance : IsProbabilityMeasure boolUniform := ⟨boolUniform_univ⟩

private theorem boolUniform_real_true : boolUniform.real {true} = 1 / 2 := by
  rw [measureReal_def, boolUniform_true]
  simp

private theorem boolUniform_real_false : boolUniform.real {false} = 1 / 2 := by
  rw [measureReal_def, boolUniform_false]
  simp

private theorem risk_allFalse :
    risk truncLoss boolUniform (meanFit (199 + 1) fun _ => false) = 1 / 2 := by
  have hfit : meanFit (199 + 1) (fun _ : Fin (199 + 1) => false) = 0 := by
    simp [meanFit, bit]
  have hinter : (fun b => truncLoss 0 b) = bit := by
    funext b
    cases b <;> norm_num [truncLoss, bit]
  have h_int : Integrable bit boolUniform :=
    Integrable.of_bound (measurable_of_finite _).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun b => by cases b <;> simp [bit])
  rw [hfit]
  show ∫ b, truncLoss 0 b ∂boolUniform = 1 / 2
  rw [hinter, MeasureTheory.integral_fintype h_int, Fintype.sum_bool,
    boolUniform_real_true, boolUniform_real_false]
  simp [bit, smul_eq_mul]

private theorem emp_allFalse :
    empiricalRisk truncLoss (fun _ : Fin (199 + 1) => false)
        (meanFit (199 + 1) fun _ => false) = 0 := by
  have hfit : meanFit (199 + 1) (fun _ : Fin (199 + 1) => false) = 0 := by
    simp [meanFit, bit]
  have h0 : ∀ i : Fin (199 + 1),
      truncLoss 0 ((fun _ : Fin (199 + 1) => false) i) = 0 := by
    intro i
    norm_num [truncLoss, bit]
  rw [hfit]
  simp only [empiricalRisk]
  rw [Finset.sum_eq_zero (fun i _ => h0 i)]
  simp

private theorem log20_lt_three : Real.log 20 < 3 := by
  have e1 : (2.715 : ℝ) < Real.exp 1 :=
    lt_of_lt_of_le (by norm_num) Real.exp_one_gt_d9.le
  have hcube : (20 : ℝ) < (Real.exp 1) ^ 3 :=
    lt_of_lt_of_le (by norm_num) (pow_le_pow_left₀ (by norm_num) e1.le 3)
  have hexp : Real.exp 3 = (Real.exp 1) ^ 3 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
    ring
  have h20 : (20 : ℝ) < Real.exp 3 := by rw [hexp]; exact hcube
  have hexp_iff : Real.exp (Real.log 20) < Real.exp 3 ↔ Real.log 20 < 3 :=
    Real.exp_lt_exp
  rw [Real.exp_log (by norm_num)] at hexp_iff
  exact hexp_iff.mp h20

private theorem corr_lt_half :
    (1 : ℝ) / 100 + 5 * √(Real.log 20 / 400) < 1 / 2 := by
  have hlogpos : (0 : ℝ) < Real.log 20 := by
    have h := Real.log_lt_log (show (0 : ℝ) < 1 by norm_num)
      (show (1 : ℝ) < 20 by norm_num)
    rwa [Real.log_one] at h
  have hU : Real.log 20 / 400 < 3 / 400 := by linarith [log20_lt_three]
  have hsqrt : √(Real.log 20 / 400) < √((3 : ℝ) / 400) :=
    Real.sqrt_lt_sqrt (div_nonneg hlogpos.le (by norm_num)) hU
  have hval : √((3 : ℝ) / 400) < 49 / 500 := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  linarith [hsqrt, hval]

example : 1 - 1 / 20 ≤ (Measure.pi fun _ : Fin (199 + 1) => boolUniform).real
    {S | risk truncLoss boolUniform (meanFit (199 + 1) S) ≤
      empiricalRisk truncLoss S (meanFit (199 + 1) S) + 1 / 100 +
      5 * √(log 20 / 400)} := by
  have hδ : (1 / 20 : ℝ) ∈ Set.Ioo 0 1 := by norm_num [Set.mem_Ioo]
  have h := IsDeletionStable.one_sub_le_measureReal_risk_le_div (ν := boolUniform)
    (measMean (199 + 1)) (measMean 199) (bddTrunc (199 + 1)) (bddTrunc 199)
    (stableMean 199) hδ
  have e_offset : (2 : ℝ) * 1 / (((199 : ℕ) : ℝ) + 1) = 1 / 100 := by norm_num
  have e_width : (4 : ℝ) * 1 + 1 = 5 := by norm_num
  have e_log : Real.log (1 / (1 / 20 : ℝ)) = Real.log 20 := by norm_num
  have e_den : (2 : ℝ) * (((199 : ℕ) : ℝ) + 1) = 400 := by norm_num
  convert h using 2
  ext S
  simp only [Set.mem_ofPred_eq, e_offset, e_width, e_log, e_den]

example : (fun _ : Fin (199 + 1) => false) ∉
    {S | risk truncLoss boolUniform (meanFit (199 + 1) S) ≤
      empiricalRisk truncLoss S (meanFit (199 + 1) S) + 1 / 100 +
      5 * √(log 20 / 400)} := by
  simp only [Set.mem_ofPred_eq, risk_allFalse, emp_allFalse]
  linarith [corr_lt_half]

-- T3: degenerate zero loss with `κ = 0` and `M = 0`.
private def zeroLoss : Unit → Unit → ℝ := fun _ _ => 0

example (ν : Measure Unit) [IsProbabilityMeasure ν] (n : ℕ) {δ : ℝ}
    (hδ : δ ∈ Set.Ioo 0 1) :
    1 - δ ≤ (Measure.pi fun _ : Fin (n + 1) => ν).real
      {S | risk zeroLoss ν (constFam (n + 1) S) ≤
        empiricalRisk zeroLoss S (constFam (n + 1) S)} := by
  have hmeas : Measurable fun p : (Fin (n + 1) → Unit) × Unit =>
      zeroLoss (constFam (n + 1) p.1) p.2 := measurable_of_finite _
  have hmeas' : Measurable fun p : (Fin n → Unit) × Unit =>
      zeroLoss (constFam n p.1) p.2 := measurable_of_finite _
  have hbdd : ∀ S z, zeroLoss (constFam (n + 1) S) z ∈ Set.Icc 0 0 :=
    fun S z => Set.mem_Icc.mpr ⟨by simp [zeroLoss], by simp [zeroLoss]⟩
  have hbdd' : ∀ S z, zeroLoss (constFam n S) z ∈ Set.Icc 0 0 :=
    fun S z => Set.mem_Icc.mpr ⟨by simp [zeroLoss], by simp [zeroLoss]⟩
  have hstab : IsDeletionStable zeroLoss (constFam (n + 1)) (constFam n)
      (0 / ((n : ℝ) + 1)) := by
    intro S i z
    simp [zeroLoss]
  have h := IsDeletionStable.one_sub_le_measureReal_risk_le_div (ν := ν) hmeas
    hmeas' hbdd hbdd' hstab hδ
  simpa using h

end CSLibExtTest.StabilityHighProbability

#print axioms IsDeletionStable.one_sub_le_measureReal_risk_le_div
