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
open scoped ENNReal

namespace MathlibExtTest.Biology.StatisticalGenetics.Breeder

/-! ### A non-vacuous model

A deterministic regression on a one-point population: mid-parent value `3`, so population
mean `3`, heritability `1/2`, offspring value `3 + (1/2) (3 - 3) = 3`. -/

/-- The witness model on the one-point space. -/
noncomputable def W : Model (Measure.dirac ()) where
  mean := 3
  h2 := 1 / 2
  parent := fun _ => 3
  offspring := fun _ => 3
  measurable_parent := measurable_const
  integrable_parent := integrable_const _
  integrable_offspring := integrable_const _
  integral_parent := by simp
  condExp_offspring := by
    refine Filter.EventuallyEq.of_eq ?_
    rw [condExp_const (Measurable.comap_le measurable_const)]
    funext _
    norm_num

/-- Selecting everyone: `S = 3 - 3 = 0`, directly and by `selectionDifferential_univ`. -/
example : W.selectionDifferential Set.univ = 0 := by
  simp [Model.selectionDifferential, W]

example : W.selectionDifferential Set.univ = 0 := W.selectionDifferential_univ

/-- Selecting everyone: `R = 3 - 3 = 0`. -/
example : W.response Set.univ = 0 := W.response_univ

/-- The breeder's equation on the witness: `R = h² S`. -/
example : W.response Set.univ = W.h2 * W.selectionDifferential Set.univ :=
  W.response_eq MeasurableSet.univ (by simp)

/-! ### Selection that changes the mean

Two equally frequent parental values `4` and `2` (population mean `3`), heritability `1/2`,
offspring value `3 + (1/2) (P - 3)`. Selecting the parents with `P ≥ 3` gives `S = 4 - 3 = 1`
and `R = 7/2 - 3 = 1/2 = h² S`; the values are computed directly from the conditional
measure. -/

/-- The uniform population on two individuals. -/
noncomputable def μ2 : Measure Bool := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false)

theorem μ2_singleton (b : Bool) : μ2 {b} = 2⁻¹ := by
  cases b <;> simp [μ2]

instance : IsProbabilityMeasure μ2 := ⟨by
  simp [μ2]
  rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]⟩

theorem integral_μ2 (f : Bool → ℝ) : ∫ b, f b ∂μ2 = (f true + f false) / 2 := by
  rw [integral_fintype Integrable.of_finite, Fintype.sum_bool]
  simp [measureReal_def, μ2_singleton]
  ring

theorem integral_cond_true (f : Bool → ℝ) : ∫ b, f b ∂μ2[|{true}] = f true := by
  rw [integral_fintype Integrable.of_finite, Fintype.sum_bool]
  simp [measureReal_def, cond_apply (measurableSet_singleton _), μ2_singleton]

/-- Parental values `4` and `2`. -/
noncomputable def P2 : Bool → ℝ := fun b => if b then 4 else 2

/-- The two-individual model. -/
noncomputable def W2 : Model μ2 where
  mean := 3
  h2 := 1 / 2
  parent := P2
  offspring := fun ω => 3 + 1 / 2 * (P2 ω - 3)
  measurable_parent := measurable_of_finite _
  integrable_parent := Integrable.of_finite
  integrable_offspring := Integrable.of_finite
  integral_parent := by
    rw [integral_μ2]
    norm_num [P2]
  condExp_offspring := by
    refine Filter.EventuallyEq.of_eq ?_
    refine condExp_of_stronglyMeasurable (measurable_of_finite P2).comap_le ?_
      Integrable.of_finite
    exact Measurable.stronglyMeasurable
      ((measurable_const.add (measurable_const.mul (measurable_id.sub measurable_const))).comp
        (comap_measurable P2))

/-- Truncation at `3` selects exactly the individual with `P = 4`. -/
theorem sel_eq : P2 ⁻¹' Set.Ici 3 = {true} := by
  ext b
  cases b <;> norm_num [P2]

/-- `S = 1`, computed from the conditional measure. -/
example : W2.selectionDifferential {true} = 1 := by
  rw [Model.selectionDifferential, integral_cond_true]
  norm_num [W2, P2]

/-- `R = 1/2`, computed from the conditional measure. -/
example : W2.response {true} = 1 / 2 := by
  rw [Model.response, integral_cond_true]
  norm_num [W2, P2]

/-- The breeder's equation applied to this selection: `R = h² S` with `h² S = 1/2 · 1`. -/
example : W2.response {true} = 1 / 2 * 1 := by
  rw [W2.response_eq (s := {true}) (by rw [← sel_eq]; exact ⟨Set.Ici 3, measurableSet_Ici, rfl⟩)
    (by simp [μ2_singleton]), Model.selectionDifferential, integral_cond_true]
  norm_num [W2, P2]

/-! ### Truncation selection in an arbitrary model -/

/-- Truncation selection: parents with `P ≥ t` are selected; the selected set is determined by
`P`, so the breeder's equation applies. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (M : Model μ)
    (t : ℝ) (h : μ (M.parent ⁻¹' Set.Ici t) ≠ 0) :
    M.response (M.parent ⁻¹' Set.Ici t) =
      M.h2 * M.selectionDifferential (M.parent ⁻¹' Set.Ici t) :=
  M.response_eq ⟨Set.Ici t, measurableSet_Ici, rfl⟩ h

/-- Boundary case: zero heritability gives no response, whatever the selection. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (M : Model μ)
    (h2 : M.h2 = 0) {s : Set Ω}
    (hs : MeasurableSet[MeasurableSpace.comap M.parent inferInstance] s) (hs0 : μ s ≠ 0) :
    M.response s = 0 := by
  rw [M.response_eq hs hs0, h2, zero_mul]

/-- Boundary (junk value outside the domain): selecting a null set gives the junk conditional
measure `0`, so `R = -μ` rather than a response; `response_eq` requires `μ s ≠ 0`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (M : Model μ)
    {s : Set Ω} (hs : μ s = 0) : M.response s = -M.mean := by
  simp [Model.response, cond_eq_zero_of_meas_eq_zero hs]

end MathlibExtTest.Biology.StatisticalGenetics.Breeder
