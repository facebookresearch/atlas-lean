/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ErdosMinimumOverlapMoser
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Motzkin–Ralston–Selfridge upper bound `0.4` for minimum overlap

The admissible pair `f t = (1 + 3 * t ^ 2) / 4`, `g t = 3 * (1 - t ^ 2) / 4`
on `[-1, 1]` (both zero elsewhere) has overlap
`2 / 5 - x ^ 3 / 8 + 3 * x ^ 5 / 160` at every `x ∈ [0, 2]`, hence pair score
at most `2 / 5`. This proves `upperBound_MRS1956_pointFour_holds`.

Source: Motzkin--Ralston--Selfridge 1956 and Optimization Problems 1b.
-/

@[expose] public section

open MeasureTheory Set

namespace MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted

private noncomputable def mrsF (t : ℝ) : ℝ :=
  (continuousSupportInterval.indicator fun t ↦ (1 + 3 * t ^ 2) / 4) t

private noncomputable def mrsG (t : ℝ) : ℝ :=
  (continuousSupportInterval.indicator fun t ↦ 3 * (1 - t ^ 2) / 4) t

private theorem mrsF_mem (t : ℝ) (ht : t ∈ continuousSupportInterval) :
    mrsF t = (1 + 3 * t ^ 2) / 4 := by
  simp [mrsF, ht]

private theorem mrsG_mem (t : ℝ) (ht : t ∈ continuousSupportInterval) :
    mrsG t = 3 * (1 - t ^ 2) / 4 := by
  simp [mrsG, ht]

private theorem mrsF_notMem (t : ℝ) (ht : t ∉ continuousSupportInterval) :
    mrsF t = 0 := by
  simp [mrsF, ht]

private theorem mrsG_notMem (t : ℝ) (ht : t ∉ continuousSupportInterval) :
    mrsG t = 0 := by
  simp [mrsG, ht]

private theorem mrs_measurable_f : AEMeasurable mrsF volume :=
  (by fun_prop : Continuous fun t : ℝ ↦ (1 + 3 * t ^ 2) / 4).measurable.indicator
    measurableSet_Icc |>.aemeasurable

private theorem mrs_measurable_g : AEMeasurable mrsG volume :=
  (by fun_prop : Continuous fun t : ℝ ↦ 3 * (1 - t ^ 2) / 4).measurable.indicator
    measurableSet_Icc |>.aemeasurable

private theorem mrs_sq_le_one (t : ℝ) (ht : t ∈ continuousSupportInterval) :
    t ^ 2 ≤ 1 := by
  have h1 : (0 : ℝ) ≤ (1 - t) * (1 + t) :=
    mul_nonneg (by linarith [ht.2]) (by linarith [ht.1])
  have hexpand : (1 - t) * (1 + t) = 1 - t ^ 2 := by ring
  rw [hexpand] at h1
  linarith [h1]

private theorem mrs_range_f (t : ℝ) : mrsF t ∈ Icc (0 : ℝ) 1 := by
  by_cases ht : t ∈ continuousSupportInterval
  · rw [mrsF_mem t ht]
    refine ⟨?_, ?_⟩
    · have hnn : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
      linarith [hnn]
    · linarith [mrs_sq_le_one t ht]
  · rw [mrsF_notMem t ht]
    exact ⟨le_rfl, zero_le_one⟩

private theorem mrs_range_g (t : ℝ) : mrsG t ∈ Icc (0 : ℝ) 1 := by
  by_cases ht : t ∈ continuousSupportInterval
  · rw [mrsG_mem t ht]
    refine ⟨?_, ?_⟩
    · linarith [mrs_sq_le_one t ht]
    · have hnn : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
      linarith [hnn]
  · rw [mrsG_notMem t ht]
    exact ⟨le_rfl, zero_le_one⟩

private theorem mrs_complementary (t : ℝ) (ht : t ∈ continuousSupportInterval) :
    mrsF t + mrsG t = 1 := by
  rw [mrsF_mem t ht, mrsG_mem t ht]
  ring

private theorem mrs_integral_f : (∫ t : ℝ, mrsF t) = 1 := by
  have h1 : (∫ t : ℝ, mrsF t) = ∫ t in Icc (-1 : ℝ) 1, (1 + 3 * t ^ 2) / 4 :=
    MeasureTheory.integral_indicator measurableSet_Icc
  rw [h1, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have h2 : (∫ t in (-1 : ℝ)..1, (1 + 3 * t ^ 2) / 4)
      = (∫ t in (-1 : ℝ)..1, (1 / 4 : ℝ)) + ∫ t in (-1 : ℝ)..1, (3 / 4 : ℝ) * t ^ 2 := by
    have heq : (fun t : ℝ ↦ (1 + 3 * t ^ 2) / 4) = fun t ↦ 1 / 4 + (3 / 4 : ℝ) * t ^ 2 := by
      funext t
      ring
    rw [heq]
    exact intervalIntegral.integral_add intervalIntegrable_const
      ((by fun_prop : Continuous fun t : ℝ ↦ (3 / 4 : ℝ) * t ^ 2).intervalIntegrable _ _)
  rw [h2]
  simp only [intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_pow,
    smul_eq_mul, Nat.cast_ofNat]
  norm_num

private theorem mrs_admissible : ContinuousAdmissible mrsF mrsG :=
  ⟨mrs_measurable_f, mrs_measurable_g, mrs_range_f, mrs_range_g, mrsF_notMem, mrsG_notMem,
    mrs_complementary, mrs_integral_f⟩

private theorem mrsF_neg (t : ℝ) : mrsF (-t) = mrsF t := by
  by_cases ht : t ∈ continuousSupportInterval
  · have hnt : -t ∈ continuousSupportInterval := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    rw [mrsF_mem (-t) hnt, mrsF_mem t ht]
    ring
  · have hnt : -t ∉ continuousSupportInterval := by
      intro h
      exact ht ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [mrsF_notMem (-t) hnt, mrsF_notMem t ht]

private theorem mrsG_neg (t : ℝ) : mrsG (-t) = mrsG t := by
  by_cases ht : t ∈ continuousSupportInterval
  · have hnt : -t ∈ continuousSupportInterval := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    rw [mrsG_mem (-t) hnt, mrsG_mem t ht]
    ring
  · have hnt : -t ∉ continuousSupportInterval := by
      intro h
      exact ht ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [mrsG_notMem (-t) hnt, mrsG_notMem t ht]

private theorem mrs_overlap_neg (x : ℝ) :
    continuousOverlap mrsF mrsG (-x) = continuousOverlap mrsF mrsG x := by
  have hsupp : ∀ y : ℝ, ∀ t : ℝ, t ∉ continuousSupportInterval →
      continuousOverlapIntegrand mrsF mrsG y t = 0 := by
    intro y t ht
    simp [continuousOverlapIntegrand, mrsF_notMem t ht]
  calc continuousOverlap mrsF mrsG (-x)
      = ∫ t, continuousOverlapIntegrand mrsF mrsG (-x) t :=
        setIntegral_eq_integral_of_forall_compl_eq_zero (hsupp (-x))
    _ = ∫ t, continuousOverlapIntegrand mrsF mrsG (-x) (-t) :=
        (integral_neg_eq_self _ volume).symm
    _ = ∫ t, continuousOverlapIntegrand mrsF mrsG x t := by
        apply integral_congr_ae
        filter_upwards with t
        simp only [continuousOverlapIntegrand]
        rw [mrsF_neg, show -x + -t = -(x + t) by ring, mrsG_neg]
    _ = continuousOverlap mrsF mrsG x :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero (hsupp x)).symm

private theorem mrs_memF (x t : ℝ) (hx0 : 0 ≤ x) (ht : t ∈ Icc (-1 : ℝ) (1 - x)) :
    t ∈ continuousSupportInterval :=
  ⟨by linarith [ht.1], by linarith [ht.2, hx0]⟩

private theorem mrs_memG (x t : ℝ) (hx0 : 0 ≤ x) (ht : t ∈ Icc (-1 : ℝ) (1 - x)) :
    x + t ∈ continuousSupportInterval :=
  ⟨by linarith [ht.1, hx0], by linarith [ht.2]⟩

private theorem mrs_overlap_formula (x : ℝ) (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    continuousOverlap mrsF mrsG x = 2 / 5 - x ^ 3 / 8 + 3 * x ^ 5 / 160 := by
  have hsuppF : ∀ t : ℝ, t ∉ continuousSupportInterval →
      continuousOverlapIntegrand mrsF mrsG x t = 0 := by
    intro t ht
    simp [continuousOverlapIntegrand, mrsF_notMem t ht]
  have hsuppI : ∀ t : ℝ, t ∉ Icc (-1 : ℝ) (1 - x) →
      continuousOverlapIntegrand mrsF mrsG x t = 0 := by
    intro t ht
    by_cases hFt : t ∈ continuousSupportInterval
    · have htx : x + t ∉ continuousSupportInterval := by
        intro h
        apply ht
        exact ⟨by linarith [hFt.1], by linarith [h.2]⟩
      simp [continuousOverlapIntegrand, mrsG_notMem (x + t) htx]
    · simp [continuousOverlapIntegrand, mrsF_notMem t hFt]
  have hA : continuousOverlap mrsF mrsG x
      = ∫ t in Icc (-1 : ℝ) (1 - x), continuousOverlapIntegrand mrsF mrsG x t := by
    calc continuousOverlap mrsF mrsG x
        = ∫ t, continuousOverlapIntegrand mrsF mrsG x t :=
          setIntegral_eq_integral_of_forall_compl_eq_zero hsuppF
      _ = ∫ t in Icc (-1 : ℝ) (1 - x), continuousOverlapIntegrand mrsF mrsG x t :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero hsuppI).symm
  have hQ : (∫ t in Icc (-1 : ℝ) (1 - x), continuousOverlapIntegrand mrsF mrsG x t)
      = ∫ t in (-1 : ℝ)..(1 - x), (3 / 16) * ((1 - x ^ 2) + (-2 * x) * t
        + (2 - 3 * x ^ 2) * t ^ 2 + (-6 * x) * t ^ 3 + (-3) * t ^ 4) := by
    have hcongr : (∫ t in Icc (-1 : ℝ) (1 - x), continuousOverlapIntegrand mrsF mrsG x t)
        = ∫ t in Icc (-1 : ℝ) (1 - x), (3 / 16) * ((1 - x ^ 2) + (-2 * x) * t
          + (2 - 3 * x ^ 2) * t ^ 2 + (-6 * x) * t ^ 3 + (-3) * t ^ 4) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      have hFt := mrsF_mem t (mrs_memF x t hx0 ht)
      have hGt := mrsG_mem (x + t) (mrs_memG x t hx0 ht)
      dsimp only [continuousOverlapIntegrand]
      rw [hFt, hGt]
      ring
    rw [hcongr, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 - x by linarith)]
  have hC : (∫ t in (-1 : ℝ)..(1 - x), (3 / 16) * ((1 - x ^ 2) + (-2 * x) * t
        + (2 - 3 * x ^ 2) * t ^ 2 + (-6 * x) * t ^ 3 + (-3) * t ^ 4))
      = 2 / 5 - x ^ 3 / 8 + 3 * x ^ 5 / 160 := by
    rw [intervalIntegral.integral_const_mul]
    have e1 : (∫ t in (-1 : ℝ)..(1 - x), (1 - x ^ 2) + (-2 * x) * t
          + (2 - 3 * x ^ 2) * t ^ 2 + (-6 * x) * t ^ 3 + (-3) * t ^ 4)
        = (∫ t in (-1 : ℝ)..(1 - x), (1 - x ^ 2) + (-2 * x) * t
            + (2 - 3 * x ^ 2) * t ^ 2 + (-6 * x) * t ^ 3)
          + ∫ t in (-1 : ℝ)..(1 - x), (-3) * t ^ 4 :=
      intervalIntegral.integral_add
        ((by fun_prop : Continuous fun t : ℝ ↦ (1 - x ^ 2) + (-2 * x) * t
          + (2 - 3 * x ^ 2) * t ^ 2 + (-6 * x) * t ^ 3).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun t : ℝ ↦ (-3 : ℝ) * t ^ 4).intervalIntegrable _ _)
    have e2 : (∫ t in (-1 : ℝ)..(1 - x), (1 - x ^ 2) + (-2 * x) * t
          + (2 - 3 * x ^ 2) * t ^ 2 + (-6 * x) * t ^ 3)
        = (∫ t in (-1 : ℝ)..(1 - x), (1 - x ^ 2) + (-2 * x) * t
            + (2 - 3 * x ^ 2) * t ^ 2)
          + ∫ t in (-1 : ℝ)..(1 - x), (-6 * x) * t ^ 3 :=
      intervalIntegral.integral_add
        ((by fun_prop : Continuous fun t : ℝ ↦ (1 - x ^ 2) + (-2 * x) * t
          + (2 - 3 * x ^ 2) * t ^ 2).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun t : ℝ ↦ (-6 * x) * t ^ 3).intervalIntegrable _ _)
    have e3 : (∫ t in (-1 : ℝ)..(1 - x), (1 - x ^ 2) + (-2 * x) * t
          + (2 - 3 * x ^ 2) * t ^ 2)
        = (∫ t in (-1 : ℝ)..(1 - x), (1 - x ^ 2) + (-2 * x) * t)
          + ∫ t in (-1 : ℝ)..(1 - x), (2 - 3 * x ^ 2) * t ^ 2 :=
      intervalIntegral.integral_add
        ((by fun_prop : Continuous fun t : ℝ ↦ (1 - x ^ 2) + (-2 * x) * t).intervalIntegrable
          _ _)
        ((by fun_prop : Continuous fun t : ℝ ↦ (2 - 3 * x ^ 2) * t ^ 2).intervalIntegrable
          _ _)
    have e4 : (∫ t in (-1 : ℝ)..(1 - x), (1 - x ^ 2) + (-2 * x) * t)
        = (∫ t in (-1 : ℝ)..(1 - x), (1 - x ^ 2))
          + ∫ t in (-1 : ℝ)..(1 - x), (-2 * x) * t :=
      intervalIntegral.integral_add intervalIntegrable_const
        ((by fun_prop : Continuous fun t : ℝ ↦ (-2 * x) * t).intervalIntegrable _ _)
    have v0 : (∫ t in (-1 : ℝ)..(1 - x), (1 - x ^ 2)) = (2 - x) * (1 - x ^ 2) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    have v1 : (∫ t in (-1 : ℝ)..(1 - x), (-2 * x) * t)
        = (-2 * x) * (((1 - x) ^ 2 - 1) / 2) := by
      rw [intervalIntegral.integral_const_mul, integral_id]
      norm_num
    have v2 : (∫ t in (-1 : ℝ)..(1 - x), (2 - 3 * x ^ 2) * t ^ 2)
        = (2 - 3 * x ^ 2) * (((1 - x) ^ 3 + 1) / 3) := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      norm_num
    have v3 : (∫ t in (-1 : ℝ)..(1 - x), (-6 * x) * t ^ 3)
        = (-6 * x) * (((1 - x) ^ 4 - 1) / 4) := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      norm_num
    have v4 : (∫ t in (-1 : ℝ)..(1 - x), (-3) * t ^ 4)
        = (-3) * (((1 - x) ^ 5 + 1) / 5) := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      norm_num
    rw [e1, e2, e3, e4, v0, v1, v2, v3, v4]
    ring
  rw [hA, hQ, hC]

private theorem mrs_overlap_le (x : ℝ) (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    continuousOverlap mrsF mrsG x ≤ 2 / 5 := by
  rw [mrs_overlap_formula x hx0 hx2]
  have hsq : x ^ 2 ≤ 4 := by
    calc x ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ hx0 hx2 2
    _ = 4 := by norm_num
  have h20 : (0 : ℝ) ≤ 20 - 3 * x ^ 2 := by linarith [hsq]
  have hnn : (0 : ℝ) ≤ x ^ 3 * (20 - 3 * x ^ 2) := mul_nonneg (pow_nonneg hx0 3) h20
  have hexpand : x ^ 3 * (20 - 3 * x ^ 2) = 20 * x ^ 3 - 3 * x ^ 5 := by ring
  rw [hexpand] at hnn
  linarith [hnn]

/-- **Motzkin–Ralston–Selfridge upper bound $0.4$ for the minimum-overlap constant.** The
continuous Erdős minimum-overlap constant $C_{1b}$ satisfies $C_{1b} \le 0.4$.

Source: Motzkin--Ralston--Selfridge 1956 and Optimization Problems 1b. -/
theorem upperBound_MRS1956_pointFour_holds : upperBound_MRS1956_pointFour := by
  change C₁ᵦ ≤ (4 : ℝ) / 10
  refine le_trans
    (continuousMinimumOverlapConstant_isUniversalLowerBound mrsF mrsG mrs_admissible) ?_
  rw [show (4 : ℝ) / 10 = 2 / 5 by norm_num]
  apply csSup_le (continuousOverlapValues_nonempty mrsF mrsG)
  rintro y ⟨x, hx, rfl⟩
  by_cases hx0 : 0 ≤ x
  · exact mrs_overlap_le x hx0 hx.2
  · have hx0' : x < 0 := lt_of_not_ge hx0
    have h1 : (0 : ℝ) ≤ -x := by linarith [hx0']
    have h2 : -x ≤ 2 := by linarith [hx.1]
    rw [← mrs_overlap_neg x]
    exact mrs_overlap_le (-x) h1 h2

end MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted
