/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BlumenthalZeroOne
import MathlibExtTest.Probability.BlumenthalZeroOneModels

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MathlibExt.Probability.BlumenthalZeroOneTest

open MathlibExt.Probability.BlumenthalZeroOne

/-- The natural filtration of `B` augmented by a measurable real-valued
variable `Z`: its value at `t` is the join of `σ(B_u : u ≤ t)` and `σ(Z)`.
The coin information is present at every positive time, hence in the germ.
The constructed zero-process/fair-coin model below realizes this boundary. -/
def augFiltration {Ω : Type*} {m : MeasurableSpace Ω} {E : Type*} [MeasurableSpace E]
    (B : NNReal → Ω → E) (hB : ∀ t, Measurable (B t)) (Z : Ω → ℝ)
    (hZ : Measurable Z) : Filtration NNReal m where
  seq t := naturalFiltration B hB t ⊔ MeasurableSpace.comap Z inferInstance
  mono' := by
    intro a b hab
    exact sup_le_sup ((naturalFiltration B hB).mono hab) le_rfl
  le' t := sup_le ((naturalFiltration B hB).le t) (measurable_iff_comap_le.mp hZ)

/-- The coin event `{Z = 1}` lies in the germ σ-algebra of the augmented
filtration, since `σ(Z)` is contained in every positive-time component. -/
theorem coin_event_mem_germ {Ω : Type*} {m : MeasurableSpace Ω} {E : Type*}
    [MeasurableSpace E] {B : NNReal → Ω → E} (hB : ∀ t, Measurable (B t))
    {Z : Ω → ℝ} (hZ : Measurable Z) :
    MeasurableSet[germSigmaAlgebraZero (augFiltration B hB Z hZ)] {ω | Z ω = 1} := by
  have hle : MeasurableSpace.comap Z inferInstance ≤
      germSigmaAlgebraZero (augFiltration B hB Z hZ) := by
    show MeasurableSpace.comap Z inferInstance ≤
      ⨅ t > (0 : NNReal), (augFiltration B hB Z hZ) t
    apply le_iInf₂
    intro t _
    exact le_sup_right
  have hmeas : MeasurableSet[MeasurableSpace.comap Z inferInstance] {ω | Z ω = 1} :=
    MeasurableSpace.measurableSet_comap.mpr ⟨{1}, measurableSet_singleton 1, rfl⟩
  exact hle _ hmeas

/-- A conditional helper: if the process contract holds for the augmented
filtration and the displayed event has probability `1/2`, that event is a
nontrivial germ event. Both substantive facts remain explicit hypotheses.
The separately constructed fair-coin/zero-process model below supplies
actual witnesses without these assumptions. This preserves the exact old
conditional proposition under the corrected process specification. -/
theorem conditional_augmented_germ_nontrivial {Ω : Type*} {m : MeasurableSpace Ω} {E : Type*}
    [MeasurableSpace E] [AddCommGroup E] [TopologicalSpace E]
    {B : NNReal → Ω → E} (hB : ∀ t, Measurable (B t)) {Z : Ω → ℝ} (hZ : Measurable Z)
    {μ : Measure Ω} {x : E}
    (hBM : IsContinuousIndependentIncrementProcess B (augFiltration B hB Z hZ) μ x)
    (hHalf : μ {ω | Z ω = 1} = 1 / 2) :
    IsContinuousIndependentIncrementProcess B (augFiltration B hB Z hZ) μ x ∧
      MeasurableSet[germSigmaAlgebraZero (augFiltration B hB Z hZ)] {ω | Z ω = 1} ∧
      μ {ω | Z ω = 1} ≠ 0 ∧ μ {ω | Z ω = 1} ≠ 1 := by
  refine ⟨hBM, coin_event_mem_germ hB hZ, ?_, ?_⟩
  · rw [hHalf]
    intro h0
    have h := congrArg ENNReal.toReal h0
    rw [ENNReal.toReal_div] at h
    norm_num at h
  · rw [hHalf]
    intro h1
    have h := congrArg ENNReal.toReal h1
    rw [ENNReal.toReal_div] at h
    norm_num at h

/-- The general zero-one theorem applies to events in the natural germ. -/
example {Ω : Type*} {m : MeasurableSpace Ω} {E : Type*} [MeasurableSpace E] [AddCommGroup E]
    [PseudoMetricSpace E] [BorelSpace E] [SecondCountableTopology E] [ContinuousAdd E]
    [ContinuousSub E] {B : NNReal → Ω → E} {𝓕 : Filtration NNReal m} {μ : Measure Ω} {x : E}
    (hBM : IsContinuousIndependentIncrementProcess B 𝓕 μ x) (hB : ∀ t, Measurable (B t))
    {A : Set Ω} (hA : MeasurableSet[naturalGerm B hB] A) :
    μ A = 0 ∨ μ A = 1 :=
  zero_one_naturalGerm hBM hB hA

/-- The concrete coin-augmented filtration is the constant top filtration. -/
theorem zeroProcess_augFiltration_eq_top :
    augFiltration zeroProcess zeroProcess_measurable coin coin_measurable = ⊤ := by
  apply Filtration.ext
  funext t
  change naturalFiltration zeroProcess zeroProcess_measurable t ⊔
    MeasurableSpace.comap coin inferInstance = (⊤ : MeasurableSpace Bool)
  simp [coin_comap_eq_top]

/-- The actual fair-Boolean zero-process model has a nontrivial augmented germ.
There is no assumed process witness or assumed event probability. -/
theorem constant_zero_augmented_countermodel :
    IsContinuousIndependentIncrementProcess zeroProcess
      (augFiltration zeroProcess zeroProcess_measurable coin coin_measurable) fairBool 0 ∧
      MeasurableSet[germSigmaAlgebraZero
        (augFiltration zeroProcess zeroProcess_measurable coin coin_measurable)] {b | coin b = 1} ∧
      fairBool {b | coin b = 1} = 1 / 2 ∧
      fairBool {b | coin b = 1} ≠ 0 ∧ fairBool {b | coin b = 1} ≠ 1 := by
  have h := conditional_augmented_germ_nontrivial zeroProcess_measurable coin_measurable
    (zeroProcess_spec _) coin_event_probability
  exact ⟨h.1, h.2.1, coin_event_probability, h.2.2.1, h.2.2.2⟩

end MathlibExt.Probability.BlumenthalZeroOneTest
