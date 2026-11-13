/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMonotoneClass

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal unitInterval

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.NeutralMonotoneClass

open MathlibExt.Probability.MarkovSemigroupProjective
open MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisherSemigroup
open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralWrightFisherRaw
open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem
open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMonotoneClass

/-! ### The path kernel, computed from the definitions -/

-- The one-time marginal of the path kernel is the transition kernel (`map_eval_rawMeasure`).
example (x : I) (t : ℝ≥0) : (wfPathKernel x).map (fun ω => ω t) = neutralKernel t x := by
  rw [wfPathKernel_apply]
  exact map_eval_rawMeasure x t

-- The evaluation functional `ω ↦ g (ω t)` integrates to the semigroup, so for it the path
-- statements reduce to the continuous one-time statements of `NeutralStrongMarkov`.
example (x : I) (t : ℝ≥0) (g : C(I, ℝ)) : ∫ ω, g (ω t) ∂rawMeasure x = wfSemigroup t g x := by
  rw [← integral_map (measurable_pi_apply t).aemeasurable g.continuous.aestronglyMeasurable,
    map_eval_rawMeasure]
  exact integral_wfTransitionKernel _ g x

-- A constant path functional integrates to its value: `rawMeasure y` is a probability measure.
example (c : ℝ) (y : I) : ∫ _ω, c ∂wfPathKernel y = c := by
  simp

/-! ### Non-vacuity: the constant family at the absorbing state `0` -/

-- From the absorbing state `0` the semigroup stays at `0`: `P_u g 0 = ∫ g d(K_u 0)`, `K_u 0 = δ₀`.
private theorem wfSemigroup_apply_zero {u : ℝ} (hu : 0 ≤ u) (g : C(I, ℝ)) :
    wfSemigroup u g 0 = g 0 := by
  have h := integral_wfTransitionKernel u g 0
  have hk : wfTransitionKernel u 0 = Measure.dirac 0 := neutralKernel_apply_zero_state ⟨u, hu⟩
  rw [hk, integral_dirac] at h
  exact h.symm

-- The constant family `Y ≡ 0` is a Markov family for every filtration and measure.
private theorem isNeutralMarkovFamily_const_zero {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝒢 : Filtration ℝ≥0 mΩ) (μ : Measure Ω) :
    IsNeutralMarkovFamily μ 𝒢 fun _ _ => (0 : I) where
  measurable _ := measurable_const
  setIntegral_eq u v huv A _ g := by
    simp only [wfSemigroup_apply_zero (sub_nonneg.2 (NNReal.coe_le_coe.2 huv)) g]

-- Hence the path law of a Markov family is not vacuous.
example {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝒢 : Filtration ℝ≥0 mΩ) (μ : Measure Ω)
    [IsFiniteMeasure μ] {A : Set Ω} (hA : MeasurableSet[𝒢 0] A) :
    (μ.restrict A).map (fun _ (_ : ℝ≥0) => (0 : I)) =
      wfPathKernel ∘ₘ (μ.restrict A).map fun _ => (0 : I) :=
  (isNeutralMarkovFamily_const_zero 𝒢 μ).map_restrict_path_eq_comp hA

private theorem projIcc_zero : projIcc (0 : ℝ) 1 zero_le_one 0 = 0 := projIcc_left _

-- The constant process at `0` satisfies the Markov hypothesis of the strong Markov theorems.
private theorem markov_const_zero {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∀ s t : ℝ≥0, s ≤ t → ∀ g : C(I, ℝ),
      μ[fun ω => g (projIcc (0 : ℝ) 1 zero_le_one ((fun _ _ => (0 : ℝ)) t ω)) | ℱ s] =ᵐ[μ]
        fun ω => wfSemigroup ((t : ℝ) - s) g
          (projIcc (0 : ℝ) 1 zero_le_one ((fun _ _ => (0 : ℝ)) s ω)) := by
  intro s t hst g
  rw [condExp_const (ℱ.le s)]
  refine Eventually.of_forall fun _ => ?_
  simp only [projIcc_zero]
  exact (wfSemigroup_apply_zero (sub_nonneg.2 (NNReal.coe_le_coe.2 hst)) g).symm

-- The whole-path strong Markov theorem applies to the constant process at every stopping time.
example {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ≥0 mΩ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    {F : SamplePath → ℝ} (hF : Measurable F) {C : ℝ} (hFC : ∀ y, ‖F y‖ ≤ C) :
    μ[{ω | τ ω ≠ ⊤}.indicator (fun ω => F fun u => projIcc (0 : ℝ) 1 zero_le_one
        (stoppedValue (fun (_ : ℝ≥0) (_ : Ω) => (0 : ℝ)) (fun ω => τ ω + u) ω)) |
        hτ.measurableSpace] =ᵐ[μ]
      {ω | τ ω ≠ ⊤}.indicator (fun ω => ∫ y, F y ∂rawMeasure (projIcc (0 : ℝ) 1 zero_le_one
        (stoppedValue (fun (_ : ℝ≥0) (_ : Ω) => (0 : ℝ)) τ ω))) :=
  condExp_indicator_path_stoppedValue_add (fun _ => continuous_const)
    (fun _ => stronglyMeasurable_const) (markov_const_zero ℱ μ) hτ hF hFC

/-! ### Boundary cases, computed from the definitions -/

section Boundary

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ}

-- The stopping time that never stops: both sides vanish identically.
example (F : SamplePath → ℝ) :
    let hτ : IsStoppingTime ℱ fun _ : Ω => (⊤ : WithTop ℝ≥0) := fun i => by simp
    μ[{_ω | (⊤ : WithTop ℝ≥0) ≠ ⊤}.indicator (fun ω => F fun u => projIcc (0 : ℝ) 1 zero_le_one
        (stoppedValue X (fun _ => (⊤ : WithTop ℝ≥0) + u) ω)) | hτ.measurableSpace] =
      {_ω | (⊤ : WithTop ℝ≥0) ≠ ⊤}.indicator (fun ω => ∫ y, F y ∂rawMeasure
        (projIcc (0 : ℝ) 1 zero_le_one (stoppedValue X (fun _ => (⊤ : WithTop ℝ≥0)) ω))) := by
  intro hτ
  simp

-- A constant path functional: the right side is `1_{τ < ∞} c`, with no Markov hypothesis.
example {τ : Ω → WithTop ℝ≥0} (c : ℝ) :
    ({ω | τ ω ≠ ⊤}.indicator fun ω =>
        ∫ _y, c ∂rawMeasure (projIcc (0 : ℝ) 1 zero_le_one (stoppedValue X τ ω))) =
      {ω | τ ω ≠ ⊤}.indicator fun _ => c := by
  simp

-- Zero times: the multi-time kernel is the point mass at the empty vector.
example (s : ℝ≥0) (t : Fin 0 → ℝ≥0) (x : I) :
    finiteChainKernel neutralKernel s t x = Measure.dirac fun i => Fin.elim0 i := by
  rw [finiteChainKernel, Kernel.deterministic_apply]

end Boundary

/-! ### The realization, with a discontinuous test function -/

-- The indicator of `[0, 1/2)` is bounded and measurable but not continuous, so it is outside the
-- class of `NeutralStrongMarkov`; the strong Markov property holds for it at every stopping
-- time of the realization.
example (x : I) {τ : SamplePath → WithTop ℝ≥0} (hτ : IsStoppingTime (naturalFiltration x) τ)
    (t : ℝ≥0) :
    (rawMeasure x)[{ω | τ ω ≠ ⊤}.indicator (fun ω =>
        (Iio (⟨1 / 2, by norm_num, by norm_num⟩ : I)).indicator (fun _ => (1 : ℝ))
          (projIcc (0 : ℝ) 1 zero_le_one (stoppedValue (modifiedProcess x) (fun ω => τ ω + t) ω))) |
        hτ.measurableSpace] =ᵐ[rawMeasure x]
      {ω | τ ω ≠ ⊤}.indicator (fun ω =>
        ∫ y, (Iio (⟨1 / 2, by norm_num, by norm_num⟩ : I)).indicator (fun _ => (1 : ℝ)) y
          ∂neutralKernel t
            (projIcc (0 : ℝ) 1 zero_le_one (stoppedValue (modifiedProcess x) τ ω))) :=
  condExp_indicator_comp_stoppedValue_add (continuous_modifiedProcess x)
    (stronglyAdapted_naturalFiltration x)
    (fun _ _ hst g => condExp_modifiedProcess_eq_wfSemigroup x hst g) hτ t
    (measurable_const.indicator measurableSet_Iio) (C := 1)
    (fun _ => (norm_indicator_le_norm_self _ _).trans (by simp))

-- Two-time functional of the realization at a stopping time: the event that the frequency at
-- time `τ + 1` does not exceed the frequency at time `τ + 2`.
example (x : I) {τ : SamplePath → WithTop ℝ≥0} (hτ : IsStoppingTime (naturalFiltration x) τ) :
    (rawMeasure x)[{ω | τ ω ≠ ⊤}.indicator (fun ω =>
        {z : Fin 2 → I | z 0 ≤ z 1}.indicator (fun _ => (1 : ℝ)) fun i =>
          projIcc (0 : ℝ) 1 zero_le_one
            (stoppedValue (modifiedProcess x) (fun ω => τ ω + ![1, 2] i) ω)) |
        hτ.measurableSpace] =ᵐ[rawMeasure x]
      {ω | τ ω ≠ ⊤}.indicator (fun ω =>
        ∫ z, {z : Fin 2 → I | z 0 ≤ z 1}.indicator (fun _ => (1 : ℝ)) z
          ∂finiteChainKernel neutralKernel 0 ![1, 2]
            (projIcc (0 : ℝ) 1 zero_le_one (stoppedValue (modifiedProcess x) τ ω))) :=
  condExp_indicator_finite_stoppedValue_add (continuous_modifiedProcess x)
    (stronglyAdapted_naturalFiltration x)
    (fun _ _ hst g => condExp_modifiedProcess_eq_wfSemigroup x hst g) hτ
    (t := ![1, 2]) (fun i j hij => by fin_cases i <;> fin_cases j <;> simp_all)
    (measurable_const.indicator (measurableSet_le (measurable_pi_apply 0) (measurable_pi_apply 1)))
    (C := 1)
    (fun _ => (norm_indicator_le_norm_self _ _).trans (by simp))

-- The unconditional path statement for the realization at a deterministic time.
example (x : I) {F : SamplePath → ℝ} (hF : Measurable F) {C : ℝ} (hFC : ∀ y, ‖F y‖ ≤ C) :
    (rawMeasure x)[{_ω | ((1 : ℝ≥0) : WithTop ℝ≥0) ≠ ⊤}.indicator (fun ω =>
        F fun u => stoppedValue (modifiedState x) (fun _ => ((1 : ℝ≥0) : WithTop ℝ≥0) + u) ω) |
        (isStoppingTime_const (naturalFiltration x) 1).measurableSpace] =ᵐ[rawMeasure x]
      {_ω | ((1 : ℝ≥0) : WithTop ℝ≥0) ≠ ⊤}.indicator (fun ω => ∫ y, F y ∂rawMeasure
        (stoppedValue (modifiedState x) (fun _ => ((1 : ℝ≥0) : WithTop ℝ≥0)) ω)) :=
  condExp_modifiedState_path_stoppedValue_add x (isStoppingTime_const _ 1) hF hFC

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.NeutralMonotoneClass
