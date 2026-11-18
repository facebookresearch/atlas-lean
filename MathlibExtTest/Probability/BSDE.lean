/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BSDE
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.BSDE
open scoped NNReal

namespace MathlibExtTest.Probability.BSDE

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The augmented Brownian filtration exists for any measurable process `B`: the hypothesis
`IsAugmentedBrownianFiltration` of the wanted BSDE theorems is satisfiable. -/
def augmentedFiltration (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (hB : ∀ t, Measurable (B t)) :
    Filtration ℝ≥0 mΩ where
  seq t := (⨆ s ≤ t, MeasurableSpace.comap (B s) inferInstance) ⊔
    MeasurableSpace.generateFrom {N | MeasurableSet N ∧ P N = 0}
  mono' _ t hst := sup_le_sup_right (iSup₂_le fun r hr ↦
    le_iSup₂ (f := fun r (_ : r ≤ t) ↦ MeasurableSpace.comap (B r) inferInstance) r
      (hr.trans hst)) _
  le' _ := sup_le (iSup₂_le fun s _ ↦ (hB s).comap_le)
    (MeasurableSpace.generateFrom_le fun _ hN ↦ hN.1)

example (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (hB : ∀ t, Measurable (B t)) :
    IsAugmentedBrownianFiltration P (augmentedFiltration P B hB) B :=
  fun _ ↦ rfl

/-- Non-vacuity of the solution notion and of the hypotheses of the comparison theorem: for the
zero generator, `(Y, Z) = (c, 0)` solves the BSDE with terminal value `c`. -/
example {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) (T : ℝ≥0) (c : ℝ) :
    IsBSDESolution P F B T (fun _ _ _ _ ↦ 0) (fun _ ↦ c) (fun _ _ ↦ c) (fun _ _ ↦ 0) :=
  isBSDESolution_const hB hBF hInd T c (fun _ _ ↦ rfl)

/-- A generator that vanishes only at `z = 0` (Peng's g-expectation condition `g(·, y, 0) ≡ 0`):
`g(t, ω, y, z) = |z|`, the generator of the `μ|z|`-expectation with `μ = 1`. -/
example {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) (T : ℝ≥0) (c : ℝ) :
    IsBSDESolution P F B T (fun _ _ _ z ↦ |z|) (fun _ ↦ c) (fun _ _ ↦ c) (fun _ _ ↦ 0) :=
  isBSDESolution_const hB hBF hInd T c (fun _ _ ↦ abs_zero)

/-- The drift must be integrable: with the generator `g(t, ω, y, z) = 1/t`, whose integral over
`[0, 1]` diverges, no pair solves the BSDE on `[0, 1]`, in particular not `Y_t = -log t`,
`Z = 0`, which satisfies the equation at every positive time. -/
example {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (ξ : Ω → ℝ) (Y Z : ℝ≥0 → Ω → ℝ) :
    ¬ IsBSDESolution P F B 1 (fun t _ _ _ ↦ (t : ℝ)⁻¹) ξ Y Z := by
  rintro ⟨-, -, -, -, hint, -⟩
  obtain ⟨ω, hω⟩ := hint.exists
  rw [NNReal.coe_one] at hω
  have hinv : IntervalIntegrable (fun u : ℝ ↦ u⁻¹) volume 0 1 := by
    refine hω.congr fun u hu ↦ ?_
    rw [Set.uIoc_of_le zero_le_one] at hu
    simp [Real.coe_toNNReal u hu.1.le]
  simp [intervalIntegrable_inv_iff] at hinv

/-! The solution notion is stated on a probability space: under the zero measure, for which
every progressive pair would solve every equation, it does not elaborate. -/

/--
error: failed to synthesize instance of type class
  IsProbabilityMeasure 0

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (F : Filtration ℝ≥0 mΩ) (B : ℝ≥0 → Ω → ℝ) : Prop :=
  IsBSDESolution (0 : Measure Ω) F B 1 (fun _ _ _ _ => 0) (fun _ => 0) (fun _ _ => 0)
    (fun _ _ => 0)

end MathlibExtTest.Probability.BSDE
