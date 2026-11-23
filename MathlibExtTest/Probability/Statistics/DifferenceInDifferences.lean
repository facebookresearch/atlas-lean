/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.DifferenceInDifferences

/-!
# Tests for 2×2 difference-in-differences identification

Four units under counting measure, treated group `{0, 1}`:

* parallel trends hold (both groups' untreated outcomes rise by `2`): the DiD of observed outcomes
  is the ATT, `7`;
* parallel trends fail (the treated group's untreated outcomes rise by `3`): the ATT is `6` but
  the DiD is `7`, off by exactly the trend gap `1`.
-/

@[expose] public section

open MeasureTheory MathlibExt.Probability.Causality
  MathlibExt.Probability.Statistics.DifferenceInDifferences

namespace MathlibExtTest.Probability.Statistics.DifferenceInDifferences

private theorem setAverage_count_G_test_helper (f : Fin 4 → ℝ) :
    (⨍ ω in ({0, 1} : Set (Fin 4)), f ω ∂(Measure.count : Measure (Fin 4))) = (f 0 + f 1) / 2 := by
  have hInt : (∫ ω in ({0, 1} : Set (Fin 4)), f ω ∂(Measure.count : Measure (Fin 4))) = f 0 + f 1 := by
    have hG : MeasurableSet ({0, 1} : Set (Fin 4)) :=
      DiscreteMeasurableSpace.forall_measurableSet _
    rw [← integral_indicator hG, integral_count, Fin.sum_univ_four]
    have h0 : (0 : Fin 4) ∈ ({0, 1} : Set (Fin 4)) := by simp
    have h1 : (1 : Fin 4) ∈ ({0, 1} : Set (Fin 4)) := by simp
    have h2 : (2 : Fin 4) ∉ ({0, 1} : Set (Fin 4)) := by simp
    have h3 : (3 : Fin 4) ∉ ({0, 1} : Set (Fin 4)) := by simp
    rw [Set.indicator_of_mem h0, Set.indicator_of_mem h1,
        Set.indicator_of_notMem h2, Set.indicator_of_notMem h3]
    simp
  have hMeas : ((Measure.count : Measure (Fin 4)).real ({0, 1} : Set (Fin 4))) = 2 := by
    have h : (Measure.count : Measure (Fin 4)) ({0, 1} : Set (Fin 4)) = 2 := by
      simp [Measure.count_apply_finite]
    simp [Measure.real, h]
  rw [setAverage_eq _ _ _, hInt, hMeas]
  simp [smul_eq_mul]
  ring

private theorem setAverage_count_Gc_test_helper (f : Fin 4 → ℝ) :
    (⨍ ω in ({0, 1} : Set (Fin 4))ᶜ, f ω ∂(Measure.count : Measure (Fin 4))) = (f 2 + f 3) / 2 := by
  have hInt : (∫ ω in (({0, 1} : Set (Fin 4))ᶜ), f ω ∂(Measure.count : Measure (Fin 4))) = f 2 + f 3 := by
    have hGc : MeasurableSet (({0, 1} : Set (Fin 4))ᶜ) :=
      DiscreteMeasurableSpace.forall_measurableSet _
    rw [← integral_indicator hGc, integral_count, Fin.sum_univ_four]
    have hGcEq : (({0, 1} : Set (Fin 4))ᶜ) = ({2, 3} : Set (Fin 4)) := by
      ext x
      fin_cases x <;> simp
    have h0 : (0 : Fin 4) ∉ (({0, 1} : Set (Fin 4))ᶜ) := by simp [hGcEq]
    have h1 : (1 : Fin 4) ∉ (({0, 1} : Set (Fin 4))ᶜ) := by simp [hGcEq]
    have h2 : (2 : Fin 4) ∈ (({0, 1} : Set (Fin 4))ᶜ) := by simp [hGcEq]
    have h3 : (3 : Fin 4) ∈ (({0, 1} : Set (Fin 4))ᶜ) := by simp [hGcEq]
    rw [Set.indicator_of_notMem h0, Set.indicator_of_notMem h1,
        Set.indicator_of_mem h2, Set.indicator_of_mem h3]
    simp
  have hMeas : ((Measure.count : Measure (Fin 4)).real (({0, 1} : Set (Fin 4))ᶜ)) = 2 := by
    have hGcEq : (({0, 1} : Set (Fin 4))ᶜ) = ({2, 3} : Set (Fin 4)) := by
      ext x
      fin_cases x <;> simp
    have h : (Measure.count : Measure (Fin 4)) (({0, 1} : Set (Fin 4))ᶜ) = 2 := by
      rw [hGcEq]
      simp [Measure.count_apply_finite]
    simp [Measure.real, h]
  rw [setAverage_eq _ _ _, hInt, hMeas]
  simp [smul_eq_mul]
  ring

def Y0pre_case1 : Fin 4 → ℝ := ![1, 3, 2, 4]
def Y1pre_case1 : Fin 4 → ℝ := ![1, 3, 2, 4]
def Y0post_case1 : Fin 4 → ℝ := ![3, 5, 4, 6]
def Y1post_case1 : Fin 4 → ℝ := ![10, 12, 0, 0]
def Y0post_case2 : Fin 4 → ℝ := ![4, 6, 4, 6]

theorem attPost_parallelTrends_test :
    attPost (Measure.count : Measure (Fin 4)) ({0, 1} : Set (Fin 4))
      Y0post_case1 Y1post_case1 = 7 := by
  unfold attPost
  have h := setAverage_count_G_test_helper (fun ω => Y1post_case1 ω - Y0post_case1 ω)
  have e0a : Y1post_case1 0 = 10 := rfl
  have e0b : Y0post_case1 0 = 3 := rfl
  have e1a : Y1post_case1 1 = 12 := rfl
  have e1b : Y0post_case1 1 = 5 := rfl
  simp only [e0a, e0b, e1a, e1b] at h
  norm_num at h
  exact h

theorem didEstimand_parallelTrends_test :
    didEstimand (Measure.count : Measure (Fin 4)) ({0, 1} : Set (Fin 4))
      (observed ({0, 1} : Set (Fin 4)) Y0pre_case1 Y1pre_case1)
      (observed ({0, 1} : Set (Fin 4)) Y0post_case1 Y1post_case1) = 7 := by
  have hG : MeasurableSet ({0, 1} : Set (Fin 4)) :=
    DiscreteMeasurableSpace.forall_measurableSet _
  have h₀pre : IntegrableOn Y0pre_case1 ({0, 1} : Set (Fin 4))
      (Measure.count : Measure (Fin 4)) :=
    IntegrableOn.of_finite (by simp)
  have h₀post : IntegrableOn Y0post_case1 ({0, 1} : Set (Fin 4))
      (Measure.count : Measure (Fin 4)) :=
    IntegrableOn.of_finite (by simp)
  have h₁post : IntegrableOn Y1post_case1 ({0, 1} : Set (Fin 4))
      (Measure.count : Measure (Fin 4)) :=
    IntegrableOn.of_finite (by simp)
  have hNA : Y1pre_case1
      =ᵐ[((Measure.count : Measure (Fin 4)).restrict ({0, 1} : Set (Fin 4)))]
      Y0pre_case1 := by
    rfl
  have hPT : (⨍ ω in ({0, 1} : Set (Fin 4)), (Y0post_case1 ω - Y0pre_case1 ω)
        ∂(Measure.count : Measure (Fin 4)))
      = ⨍ ω in ({0, 1} : Set (Fin 4))ᶜ, (Y0post_case1 ω - Y0pre_case1 ω)
        ∂(Measure.count : Measure (Fin 4)) := by
    have hGavg := setAverage_count_G_test_helper (fun ω => Y0post_case1 ω - Y0pre_case1 ω)
    have hGcavg := setAverage_count_Gc_test_helper (fun ω => Y0post_case1 ω - Y0pre_case1 ω)
    have e0post : Y0post_case1 0 = 3 := rfl
    have e0pre : Y0pre_case1 0 = 1 := rfl
    have e1post : Y0post_case1 1 = 5 := rfl
    have e1pre : Y0pre_case1 1 = 3 := rfl
    have e2post : Y0post_case1 2 = 4 := rfl
    have e2pre : Y0pre_case1 2 = 2 := rfl
    have e3post : Y0post_case1 3 = 6 := rfl
    have e3pre : Y0pre_case1 3 = 4 := rfl
    simp only [e0post, e0pre, e1post, e1pre] at hGavg
    simp only [e2post, e2pre, e3post, e3pre] at hGcavg
    norm_num at hGavg hGcavg
    rw [hGavg, hGcavg]
  have hAtt := attPost_parallelTrends_test
  have hId := didEstimand_observed_eq_attPost hG h₀pre h₀post h₁post hNA hPT
  rw [hId]
  exact hAtt

theorem attPost_parallelTrendsFail_test :
    attPost (Measure.count : Measure (Fin 4)) ({0, 1} : Set (Fin 4))
      Y0post_case2 Y1post_case1 = 6 := by
  unfold attPost
  have h := setAverage_count_G_test_helper (fun ω => Y1post_case1 ω - Y0post_case2 ω)
  have e0a : Y1post_case1 0 = 10 := rfl
  have e0b : Y0post_case2 0 = 4 := rfl
  have e1a : Y1post_case1 1 = 12 := rfl
  have e1b : Y0post_case2 1 = 6 := rfl
  simp only [e0a, e0b, e1a, e1b] at h
  norm_num at h
  exact h

theorem didEstimand_gap_parallelTrendsFail_test :
    didEstimand (Measure.count : Measure (Fin 4)) ({0, 1} : Set (Fin 4))
      Y0pre_case1 Y0post_case2 = 1 := by
  unfold didEstimand
  have hGavg := setAverage_count_G_test_helper (fun ω => Y0post_case2 ω - Y0pre_case1 ω)
  have hGcavg := setAverage_count_Gc_test_helper (fun ω => Y0post_case2 ω - Y0pre_case1 ω)
  have e0post : Y0post_case2 0 = 4 := rfl
  have e0pre : Y0pre_case1 0 = 1 := rfl
  have e1post : Y0post_case2 1 = 6 := rfl
  have e1pre : Y0pre_case1 1 = 3 := rfl
  have e2post : Y0post_case2 2 = 4 := rfl
  have e2pre : Y0pre_case1 2 = 2 := rfl
  have e3post : Y0post_case2 3 = 6 := rfl
  have e3pre : Y0pre_case1 3 = 4 := rfl
  simp only [e0post, e0pre, e1post, e1pre] at hGavg
  simp only [e2post, e2pre, e3post, e3pre] at hGcavg
  norm_num at hGavg hGcavg
  rw [hGavg, hGcavg]
  norm_num

theorem didEstimand_parallelTrendsFail_test :
    didEstimand (Measure.count : Measure (Fin 4)) ({0, 1} : Set (Fin 4))
      (observed ({0, 1} : Set (Fin 4)) Y0pre_case1 Y1pre_case1)
      (observed ({0, 1} : Set (Fin 4)) Y0post_case2 Y1post_case1) = 7 := by
  have hG : MeasurableSet ({0, 1} : Set (Fin 4)) :=
    DiscreteMeasurableSpace.forall_measurableSet _
  have h₀pre : IntegrableOn Y0pre_case1 ({0, 1} : Set (Fin 4))
      (Measure.count : Measure (Fin 4)) :=
    IntegrableOn.of_finite (by simp)
  have h₀post : IntegrableOn Y0post_case2 ({0, 1} : Set (Fin 4))
      (Measure.count : Measure (Fin 4)) :=
    IntegrableOn.of_finite (by simp)
  have h₁post : IntegrableOn Y1post_case1 ({0, 1} : Set (Fin 4))
      (Measure.count : Measure (Fin 4)) :=
    IntegrableOn.of_finite (by simp)
  have hNA : Y1pre_case1
      =ᵐ[((Measure.count : Measure (Fin 4)).restrict ({0, 1} : Set (Fin 4)))]
      Y0pre_case1 := by
    rfl
  have hAdd := didEstimand_observed_eq_attPost_add hG h₀pre h₀post h₁post hNA
  have hAtt := attPost_parallelTrendsFail_test
  have hGap := didEstimand_gap_parallelTrendsFail_test
  rw [hAdd, hAtt, hGap]
  norm_num

theorem didEstimand_ne_attPost_parallelTrendsFail_test :
    didEstimand (Measure.count : Measure (Fin 4)) ({0, 1} : Set (Fin 4))
      (observed ({0, 1} : Set (Fin 4)) Y0pre_case1 Y1pre_case1)
      (observed ({0, 1} : Set (Fin 4)) Y0post_case2 Y1post_case1)
      ≠ attPost (Measure.count : Measure (Fin 4)) ({0, 1} : Set (Fin 4))
        Y0post_case2 Y1post_case1 := by
  rw [didEstimand_parallelTrendsFail_test, attPost_parallelTrendsFail_test]
  norm_num

end MathlibExtTest.Probability.Statistics.DifferenceInDifferences
