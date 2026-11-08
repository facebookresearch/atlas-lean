/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ErdosMinimumOverlapConstant

/-! Actual continuous inputs and the uniform balanced-partition interface. -/

@[expose] public section

open MeasureTheory Set

namespace MathlibExtTest.NumberTheory.ErdosMinimumOverlapAsymptotic

open MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted

example (f g : ℝ → ℝ) (hf : AEMeasurable f volume) (hg : AEMeasurable g volume)
    (hrf : ∀ t, f t ∈ Icc (0 : ℝ) 1) (hrg : ∀ t, g t ∈ Icc (0 : ℝ) 1)
    (hzf : ∀ t, t ∉ continuousSupportInterval → f t = 0)
    (hzg : ∀ t, t ∉ continuousSupportInterval → g t = 0)
    (hcomp : ∀ t ∈ continuousSupportInterval, f t + g t = 1)
    (hmass : (∫ t : ℝ, f t) = 1) : ContinuousAdmissible f g :=
  ⟨hf, hg, hrf, hrg, hzf, hzg, hcomp, hmass⟩

example {f g : ℝ → ℝ} (h : ContinuousAdmissible f g) (x : ℝ) :
    IntegrableOn (continuousOverlapIntegrand f g x) continuousSupportInterval :=
  h.overlap_integrable x

private noncomputable def halfIndicator (t : ℝ) : ℝ :=
  continuousSupportInterval.indicator (fun _ => (1 : ℝ) / 2) t

private theorem halfIndicator_admissible : ContinuousAdmissible halfIndicator halfIndicator := by
  have hmeas : Measurable halfIndicator := measurable_const.indicator measurableSet_Icc
  have hrange : ∀ t, halfIndicator t ∈ Icc (0 : ℝ) 1 := by
    intro t
    by_cases ht : t ∈ continuousSupportInterval
    · simp [halfIndicator, ht]
      norm_num
    · simp [halfIndicator, ht]
  have hzero : ∀ t, t ∉ continuousSupportInterval → halfIndicator t = 0 := by
    intro t ht
    simp [halfIndicator, ht]
  refine ⟨hmeas.aemeasurable, hmeas.aemeasurable, hrange, hrange, hzero, hzero, ?_, ?_⟩
  · intro t ht
    simp [halfIndicator, ht]
    norm_num
  · simp [halfIndicator, continuousSupportInterval, MeasureTheory.integral_indicator]
    norm_num

example : ContinuousAdmissible halfIndicator halfIndicator := halfIndicator_admissible

example : (∫ t : ℝ, halfIndicator t) = 1 := halfIndicator_admissible.integral_f

example : continuousOverlap halfIndicator halfIndicator 0 = (1 : ℝ) / 2 := by
  have hkernel : ∀ t ∈ continuousSupportInterval,
      continuousOverlapIntegrand halfIndicator halfIndicator 0 t = (1 : ℝ) / 4 := by
    intro t ht
    simp [continuousOverlapIntegrand, halfIndicator, ht]
    norm_num
  calc
    continuousOverlap halfIndicator halfIndicator 0 =
        ∫ t in continuousSupportInterval, (1 : ℝ) / 4 := by
      exact setIntegral_congr_fun measurableSet_Icc hkernel
    _ = (1 : ℝ) / 2 := by norm_num [continuousSupportInterval]

example : DiscreteUniversalLowerBound 0 := discreteUniversalLowerBound_zero

example (c : ℝ) : DiscreteUniversalLowerBound c ↔
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ A B : Finset ℤ,
        Disjoint A B → A ∪ B = Finset.Icc (1 : ℤ) (2 * N) → A.card = B.card →
          ∃ x : ℤ, (c - ε) * (N : ℝ) ≤ (Overlap A B x : ℝ) := Iff.rfl

example : Disjoint ({1} : Finset ℤ) {2} ∧
    ({1} : Finset ℤ) ∪ {2} = Finset.Icc (1 : ℤ) (2 * (1 : ℕ)) ∧
    ({1} : Finset ℤ).card = ({2} : Finset ℤ).card := by decide

example : Disjoint ({1, 2} : Finset ℤ) {3, 4} ∧
    ({1, 2} : Finset ℤ) ∪ {3, 4} = Finset.Icc (1 : ℤ) (2 * (2 : ℕ)) ∧
    ({1, 2} : Finset ℤ).card = ({3, 4} : Finset ℤ).card := by decide

example (ε : ℝ) (hε : 0 < ε) : ∃ x : ℤ,
    (0 - ε) * (1 : ℝ) ≤ (Overlap ({1} : Finset ℤ) {2} x : ℝ) := by
  refine ⟨-1, ?_⟩
  norm_num [Overlap]
  linarith

example (ε : ℝ) (hε : 0 < ε) : ∃ x : ℤ,
    (0 - ε) * (2 : ℝ) ≤ (Overlap ({1, 2} : Finset ℤ) {3, 4} x : ℝ) := by
  refine ⟨-2, ?_⟩
  norm_num [Overlap]
  linarith

end MathlibExtTest.NumberTheory.ErdosMinimumOverlapAsymptotic

#eval IO.println "C1B_ACTUAL_CONTINUOUS_DISCRETE_EXECUTED examples=11 mass=1 overlap_at_zero=1/2 sizes=1,2"
