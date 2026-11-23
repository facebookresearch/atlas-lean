/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.Measure.ParamSmooth

open MeasureTheory

universe uX uM uP uE

section

variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopology X]
  {M : Type uM} [NormedAddCommGroup M] [NormedSpace ℝ M]
  {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The parameter-integral API accepts independently universe-polymorphic normed spaces. -/
example (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (c : X → M) (hc : Continuous c) (w : X → ℝ) (hw : Continuous w)
    (hwc : HasCompactSupport w) (Ψ : M × P → E) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΨc : HasCompactSupport Ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : P ↦ ∫ x, w x • Ψ (c x, p) ∂μ) :=
  MeasureTheory.contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport
    μ c hc w hw hwc Ψ hΨ hΨc

end

/-- A zero-function smoke test of smoothness of parameter integrals. -/
example : ContDiff ℝ (⊤ : ℕ∞)
    (fun _p : ℝ => ∫ _x : ℝ, (0 : ℝ) • (0 : ℝ) ∂(volume : Measure ℝ)) := by
  have h := MeasureTheory.contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport
    (X := ℝ) (μ := volume) (M := ℝ) (P := ℝ) (E := ℝ)
    (fun _ => (0 : ℝ)) continuous_const (fun _ => (0 : ℝ)) continuous_const
    (by simp [HasCompactSupport]) (fun _ => (0 : ℝ)) contDiff_const
    (by simp [HasCompactSupport])
  exact h
