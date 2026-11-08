/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ErdosMinimumOverlapConstant

/-!
Characterization fixtures adapted from the retained Codex C1b boundary probes.
They are committed before the API placement change. The baseline import is
retargeted to the implemented MathlibExt model after that move.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace MathlibExtTest.NumberTheory.ErdosMinimumOverlapConstant

open MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted

private noncomputable def halfIndicator (t : ℝ) : ℝ :=
  (continuousSupportInterval.indicator fun _ => (1 : ℝ) / 2) t

private theorem halfIndicator_measurable : Measurable halfIndicator := by
  exact measurable_const.indicator measurableSet_Icc

private theorem halfIndicator_range (t : ℝ) : halfIndicator t ∈ Icc (0 : ℝ) 1 := by
  by_cases ht : t ∈ continuousSupportInterval
  · simp [halfIndicator, ht]
    norm_num
  · simp [halfIndicator, ht]

private theorem halfIndicator_zero_outside (t : ℝ)
    (ht : t ∉ continuousSupportInterval) : halfIndicator t = 0 := by
  simp [halfIndicator, ht]

private theorem halfIndicator_integral : (∫ t : ℝ, halfIndicator t) = 1 := by
  simp [halfIndicator, continuousSupportInterval, MeasureTheory.integral_indicator]
  norm_num

example : ContinuousAdmissible halfIndicator halfIndicator := by
  refine ⟨halfIndicator_measurable.aemeasurable, halfIndicator_measurable.aemeasurable,
    halfIndicator_range, halfIndicator_range, halfIndicator_zero_outside,
    halfIndicator_zero_outside, ?_, halfIndicator_integral⟩
  intro t ht
  simp [halfIndicator, ht]
  norm_num

example : continuousOverlapIntegrand halfIndicator halfIndicator 0 0 = (1 : ℝ) / 4 := by
  norm_num [continuousOverlapIntegrand, halfIndicator, continuousSupportInterval]

example : continuousOverlapIntegrand (fun t => t) (fun t => t) 1 2 = (6 : ℝ) := by
  norm_num [continuousOverlapIntegrand]

example : Overlap ({1} : Finset ℤ) {2} (-1) = 1 := by decide

example : Overlap ({1} : Finset ℤ) {2} 1 = 0 := by decide

example : Overlap ({1, 2} : Finset ℤ) {3, 4} (-2) = 2 := by decide

example : continuousTranslationInterval.Nonempty := by
  exact ⟨0, by norm_num [continuousTranslationInterval]⟩

example (f g : ℝ → ℝ) : (continuousOverlapValues f g).Nonempty :=
  continuousOverlapValues_nonempty f g

example {f g : ℝ → ℝ} (h : ContinuousAdmissible f g) : Integrable f :=
  h.integrable_f

example {f g : ℝ → ℝ} (h : ContinuousAdmissible f g) : Integrable g :=
  h.integrable_g

example {f g : ℝ → ℝ} (h : ContinuousAdmissible f g) :
    ∀ x ∈ continuousTranslationInterval,
      IntegrableOn (continuousOverlapIntegrand f g x) continuousSupportInterval := by
  intro x _
  exact h.overlap_integrable x

example {f g : ℝ → ℝ} (h : ContinuousAdmissible f g) :
    ∀ y ∈ continuousOverlapValues f g, y ∈ Icc (0 : ℝ) 1 :=
  h.overlapValues_mem_unit

example : continuousValidLowerBounds.Nonempty :=
  continuousValidLowerBounds_nonempty

example : ContinuousUniversalLowerBound C₁ᵦ :=
  continuousMinimumOverlapConstant_isUniversalLowerBound

example : IsGreatest continuousValidLowerBounds C₁ᵦ :=
  continuousMinimumOverlapConstant_isGreatest

example : (-2 : ℝ) ∈ continuousTranslationInterval := by
  norm_num [continuousTranslationInterval]

example : (2 : ℝ) ∈ continuousTranslationInterval := by
  norm_num [continuousTranslationInterval]

example (f g : ℝ → ℝ) (hf : ¬ AEMeasurable f volume) : ¬ ContinuousAdmissible f g := by
  intro h
  exact hf h.measurable_f

example (f g : ℝ → ℝ) (hg : ¬ AEMeasurable g volume) : ¬ ContinuousAdmissible f g := by
  intro h
  exact hg h.measurable_g

example (f g : ℝ → ℝ) (t : ℝ) (ht : f t ∉ Icc (0 : ℝ) 1) :
    ¬ ContinuousAdmissible f g := by
  intro h
  exact ht (h.range_f t)

example (f g : ℝ → ℝ) (t : ℝ) (ht : g t ∉ Icc (0 : ℝ) 1) :
    ¬ ContinuousAdmissible f g := by
  intro h
  exact ht (h.range_g t)

example (f g : ℝ → ℝ) (t : ℝ) (ht : t ∉ continuousSupportInterval)
    (hft : f t ≠ 0) : ¬ ContinuousAdmissible f g := by
  intro h
  exact hft (h.zero_outside_f t ht)

example (f g : ℝ → ℝ) (t : ℝ) (ht : t ∉ continuousSupportInterval)
    (hgt : g t ≠ 0) : ¬ ContinuousAdmissible f g := by
  intro h
  exact hgt (h.zero_outside_g t ht)

example (f g : ℝ → ℝ) (t : ℝ) (ht : t ∈ continuousSupportInterval)
    (hbad : f t + g t ≠ 1) : ¬ ContinuousAdmissible f g := by
  intro h
  exact hbad (h.complementary t ht)

example (f g : ℝ → ℝ) (hbad : (∫ t : ℝ, f t) ≠ 1) :
    ¬ ContinuousAdmissible f g := by
  intro h
  exact hbad h.integral_f

example (g : ℝ → ℝ) : ¬ ContinuousAdmissible (fun _ => 0) g := by
  intro h
  have hi := h.integral_f
  norm_num at hi

example (g : ℝ → ℝ) : ¬ ContinuousAdmissible (fun _ => 1) g := by
  intro h
  have hout : (2 : ℝ) ∉ continuousSupportInterval := by
    norm_num [continuousSupportInterval]
  have hz := h.zero_outside_f 2 hout
  norm_num at hz

example : MaxOverlap {1} {2} = 1 := by
  apply le_antisymm
  · apply ciSup_le
    intro k
    calc Overlap {1} {2} k ≤ (({1} : Finset ℤ).product {2}).card :=
          Finset.card_filter_le _ _
      _ = 1 := by decide
  · have h : Overlap {1} {2} (-1) = 1 := by decide
    rw [← h]
    exact Overlap_le_MaxOverlap _ _ _

example : M 1 = 1 := by
  apply le_antisymm
  · calc M 1 ≤ MaxOverlap {1} {2} :=
          M_le_MaxOverlap 1 {1} {2} (by decide) (by decide) rfl
      _ = 1 := by
          apply le_antisymm
          · apply ciSup_le
            intro k
            calc Overlap {1} {2} k ≤ (({1} : Finset ℤ).product {2}).card :=
                  Finset.card_filter_le _ _
              _ = 1 := by decide
          · have h : Overlap {1} {2} (-1) = 1 := by decide
            rw [← h]
            exact Overlap_le_MaxOverlap _ _ _
  · apply le_csInf (balancedPartition_nonempty 1)
    rintro v ⟨A, B, hd, hu, hc, rfl⟩
    have hcard : A.card = 1 := by
      have hunion : (A ∪ B).card = 2 := by
        rw [hu]
        decide
      have hdisj := Finset.card_union_of_disjoint hd
      omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < B.card)
    calc (1 : ℕ) ≤ Overlap A B (a - b) := by
          apply Finset.one_le_card.mpr
          refine ⟨(a, b), ?_⟩
          simp [Overlap, ha, hb]
      _ ≤ MaxOverlap A B := Overlap_le_MaxOverlap A B (a - b)

end MathlibExtTest.NumberTheory.ErdosMinimumOverlapConstant

#eval IO.println "C1B_CHARACTERIZATION_EXECUTED examples=27 mass=1 finite_difference_cases=3"
