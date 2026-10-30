/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.Breeder

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Biology.StatisticalGenetics.Breeder

namespace MathlibExtTest.Biology.StatisticalGenetics.Breeder

/-! ### A non-vacuous model

A deterministic regression on a one-point population: mid-parent value `3`, population mean
`1`, heritability `1/2`, offspring value `1 + (1/2) (3 - 1) = 2`. -/

/-- The witness model on the one-point space. -/
noncomputable def W : Model (Measure.dirac ()) where
  mean := 1
  h2 := 1 / 2
  parent := fun _ => 3
  offspring := fun _ => 2
  measurable_parent := measurable_const
  integrable_parent := integrable_const _
  integrable_offspring := integrable_const _
  condExp_offspring := by
    refine Filter.EventuallyEq.of_eq ?_
    rw [condExp_const (Measurable.comap_le measurable_const)]
    funext _
    norm_num

/-- Selecting everyone: `S = 3 - 1 = 2`. -/
example : W.selectionDifferential Set.univ = 2 := by
  simp [Model.selectionDifferential, W]
  norm_num

/-- Selecting everyone: `R = 2 - 1 = 1`. -/
example : W.response Set.univ = 1 := by
  simp [Model.response, W]
  norm_num

/-- The breeder's equation on the witness: `R = h² S = (1/2) * 2`. -/
example : W.response Set.univ = W.h2 * W.selectionDifferential Set.univ :=
  W.response_eq MeasurableSet.univ (by simp)

/-! ### Truncation selection in an arbitrary model -/

/-- Truncation selection: parents with `P ≥ t` are selected; the selected set is determined by
`P`, so the breeder's equation applies. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] (M : Model μ)
    (t : ℝ) (h : μ (M.parent ⁻¹' Set.Ici t) ≠ 0) :
    M.response (M.parent ⁻¹' Set.Ici t) =
      M.h2 * M.selectionDifferential (M.parent ⁻¹' Set.Ici t) :=
  M.response_eq ⟨Set.Ici t, measurableSet_Ici, rfl⟩ h

/-- Boundary case: zero heritability gives no response, whatever the selection. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] (M : Model μ)
    (h2 : M.h2 = 0) {s : Set Ω}
    (hs : MeasurableSet[MeasurableSpace.comap M.parent inferInstance] s) (hs0 : μ s ≠ 0) :
    M.response s = 0 := by
  rw [M.response_eq hs hs0, h2, zero_mul]

/-- Boundary (junk value outside the domain): selecting a null set gives the junk conditional
measure `0`, so `R = -μ` rather than a response; `response_eq` requires `μ s ≠ 0`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (M : Model μ) {s : Set Ω}
    (hs : μ s = 0) : M.response s = -M.mean := by
  simp [Model.response, cond_eq_zero_of_meas_eq_zero hs]

end MathlibExtTest.Biology.StatisticalGenetics.Breeder
