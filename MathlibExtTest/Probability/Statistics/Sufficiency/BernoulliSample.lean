/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
public import MathlibExt.Probability.Statistics.Sufficiency.BernoulliSample

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.Sufficiency.BernoulliSample

open MathlibExt.Probability.Statistics.Sufficiency

open MeasureTheory

open scoped ENNReal

/-- Fixture A (through the main theorem): the two-toss count is sufficient over the
closed family (endpoints included). -/
example :
    IsSufficient (MeasurableSpace.comap (bernoulliCount 2) inferInstance)
      (fun p : Set.Icc (0 : ℝ) 1 =>
        (((bernoulliFamily 2).law p : Measure (Fin 2 → Bool)))) := by
  exact bernoulliFamily_count_sufficient 2

/-- Fixture B (boundary): the `n = 0` count is sufficient, by the main theorem on the
one-point sample space. -/
example :
    IsSufficient (MeasurableSpace.comap (bernoulliCount 0) inferInstance)
      (fun p : Set.Icc (0 : ℝ) 1 =>
        (((bernoulliFamily 0).law p : Measure (Fin 0 → Bool)))) := by
  exact bernoulliFamily_count_sufficient 0

/-- Fixture E (endpoint `p = 0`): the endpoint law is normalized. -/
example : IsProbabilityMeasure
    ((bernoulliFamily 2).law (⟨0, le_rfl, zero_le_one⟩ : Set.Icc (0 : ℝ) 1)) :=
  ProbabilityTheory.NormalizedDensityFamily.isProbabilityMeasure_law _ _

/-- Fixture F (endpoint `p = 1`): the endpoint law is normalized. -/
example : IsProbabilityMeasure
    ((bernoulliFamily 2).law (⟨1, zero_le_one, le_rfl⟩ : Set.Icc (0 : ℝ) 1)) :=
  ProbabilityTheory.NormalizedDensityFamily.isProbabilityMeasure_law _ _

/-- Fixture G (endpoint `p = 0` use): the all-false sample carries the full mass,
exercising the `0 ^ 0 = 1` pow convention through the public density. -/
example : (bernoulliFamily 2).dens
    (⟨0, le_rfl, zero_le_one⟩ : Set.Icc (0 : ℝ) 1) ![false, false] = 1 := by
  have hp0val : ((⟨0, le_rfl, zero_le_one⟩ : Set.Icc (0 : ℝ) 1)).val = (0 : ℝ) := rfl
  have cT : (Finset.univ.filter fun i : Fin 2 => ![false, false] i = true).card = 0 := by
    decide
  have cF : (Finset.univ.filter fun i : Fin 2 => ![false, false] i = false).card = 2 := by
    decide
  show ENNReal.ofReal ((((⟨0, le_rfl, zero_le_one⟩ : Set.Icc (0 : ℝ) 1)).val ^
      (Finset.univ.filter fun i : Fin 2 => ![false, false] i = true).card) *
      ((1 - ((⟨0, le_rfl, zero_le_one⟩ : Set.Icc (0 : ℝ) 1)).val) ^
      (Finset.univ.filter fun i : Fin 2 => ![false, false] i = false).card)) = 1
  rw [cT, cF, hp0val]
  simp

/-- Fixture H (endpoint `p = 1` use): the all-true sample carries the full mass,
exercising the `(1 - 1) ^ (2 - 2) = 0 ^ 0 = 1` pow convention through the public density. -/
example : (bernoulliFamily 2).dens
    (⟨1, zero_le_one, le_rfl⟩ : Set.Icc (0 : ℝ) 1) ![true, true] = 1 := by
  have hp1val : ((⟨1, zero_le_one, le_rfl⟩ : Set.Icc (0 : ℝ) 1)).val = (1 : ℝ) := rfl
  have cT : (Finset.univ.filter fun i : Fin 2 => ![true, true] i = true).card = 2 := by
    decide
  have cF : (Finset.univ.filter fun i : Fin 2 => ![true, true] i = false).card = 0 := by
    decide
  show ENNReal.ofReal ((((⟨1, zero_le_one, le_rfl⟩ : Set.Icc (0 : ℝ) 1)).val ^
      (Finset.univ.filter fun i : Fin 2 => ![true, true] i = true).card) *
      ((1 - ((⟨1, zero_le_one, le_rfl⟩ : Set.Icc (0 : ℝ) 1)).val) ^
      (Finset.univ.filter fun i : Fin 2 => ![true, true] i = false).card)) = 1
  rw [cT, cF, hp1val]
  simp

/-- Fixture C (use): the count statistic computes correctly on a concrete sample. -/
example : bernoulliCount 2 ![true, false] = 1 := by
  decide

/-- Fixture D (counter-case): no factorization through the first toss alone can give the
joint law — the two samples agree on the first toss but carry different θ-dependent
densities. Every bound variable occurs in the conclusion. -/
example :
    ¬ ∃ g : Set.Icc (0 : ℝ) 1 → Bool → ℝ≥0∞, ∀ p : Set.Icc (0 : ℝ) 1,
      ((bernoulliFamily 2).law p) = Measure.count.withDensity
        (fun ω : Fin 2 → Bool => g p (ω 0) * 1) := by
  rintro ⟨g, hg⟩
  let p0 : Set.Icc (0 : ℝ) 1 := ⟨1/4, by norm_num [Set.mem_Icc]⟩
  let ω1 : Fin 2 → Bool := ![true, true]
  let ω2 : Fin 2 → Bool := ![true, false]
  have hmeas := hg p0
  have hlaw : ((bernoulliFamily 2).law p0 : Measure (Fin 2 → Bool)) =
      Measure.count.withDensity ((bernoulliFamily 2).dens p0) := rfl
  rw [hlaw] at hmeas
  have hcongr1 := congrArg (fun μ : Measure (Fin 2 → Bool) => μ {ω1}) hmeas
  have hcongr2 := congrArg (fun μ : Measure (Fin 2 → Bool) => μ {ω2}) hmeas
  have hL1 : (Measure.count.withDensity ((bernoulliFamily 2).dens p0)) {ω1} =
      (bernoulliFamily 2).dens p0 ω1 := by
    rw [MeasureTheory.withDensity_apply _ (measurableSet_singleton _),
      MeasureTheory.lintegral_singleton _ _, Measure.count_singleton _, mul_one]
  have hR1 : (Measure.count.withDensity
      (fun ω : Fin 2 → Bool => g p0 (ω 0) * 1)) {ω1} = g p0 (ω1 0) * 1 := by
    rw [MeasureTheory.withDensity_apply _ (measurableSet_singleton _),
      MeasureTheory.lintegral_singleton _ _, Measure.count_singleton _, mul_one]
  have hL2 : (Measure.count.withDensity ((bernoulliFamily 2).dens p0)) {ω2} =
      (bernoulliFamily 2).dens p0 ω2 := by
    rw [MeasureTheory.withDensity_apply _ (measurableSet_singleton _),
      MeasureTheory.lintegral_singleton _ _, Measure.count_singleton _, mul_one]
  have hR2 : (Measure.count.withDensity
      (fun ω : Fin 2 → Bool => g p0 (ω 0) * 1)) {ω2} = g p0 (ω2 0) * 1 := by
    rw [MeasureTheory.withDensity_apply _ (measurableSet_singleton _),
      MeasureTheory.lintegral_singleton _ _, Measure.count_singleton _, mul_one]
  rw [hL1, hR1] at hcongr1
  rw [hL2, hR2] at hcongr2
  have h01 : ω1 0 = true := by decide
  have h02 : ω2 0 = true := by decide
  rw [h01] at hcongr1
  rw [h02] at hcongr2
  have heq : (bernoulliFamily 2).dens p0 ω1 =
      (bernoulliFamily 2).dens p0 ω2 := by
    rw [hcongr1, hcongr2]
  have hne : (bernoulliFamily 2).dens p0 ω1 ≠
      (bernoulliFamily 2).dens p0 ω2 := by
    have c1t : (Finset.univ.filter fun i : Fin 2 => ω1 i = true).card = 2 := by
      decide
    have c1f : (Finset.univ.filter fun i : Fin 2 => ω1 i = false).card = 0 := by
      decide
    have c2t : (Finset.univ.filter fun i : Fin 2 => ω2 i = true).card = 1 := by
      decide
    have c2f : (Finset.univ.filter fun i : Fin 2 => ω2 i = false).card = 1 := by
      decide
    have hp0val : p0.val = (1/4 : ℝ) := rfl
    show ENNReal.ofReal ((p0.val ^
        (Finset.univ.filter fun i : Fin 2 => ω1 i = true).card) *
        ((1 - p0.val) ^ (Finset.univ.filter fun i : Fin 2 => ω1 i = false).card)) ≠
      ENNReal.ofReal ((p0.val ^
        (Finset.univ.filter fun i : Fin 2 => ω2 i = true).card) *
        ((1 - p0.val) ^ (Finset.univ.filter fun i : Fin 2 => ω2 i = false).card))
    rw [c1t, c1f, c2t, c2f, hp0val]
    have h1 : ((1/4 : ℝ) ^ 2 * ((1 - 1/4) ^ 0)) = 1/16 := by norm_num
    have h2 : ((1/4 : ℝ) ^ 1 * ((1 - 1/4) ^ 1)) = 3/16 := by norm_num
    rw [h1, h2]
    intro hcon
    have hcon' : (1/16 : ℝ) = 3/16 :=
      (ENNReal.ofReal_eq_ofReal_iff (by norm_num) (by norm_num)).mp hcon
    norm_num at hcon'
  exact hne heq

end MathlibExtTest.Probability.Statistics.Sufficiency.BernoulliSample
