/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Diffusion.SelectionMonotoneClass

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal unitInterval

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.SelectionMonotoneClass

open MathlibExt.Probability.MarkovSemigroupProjective
open MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisherSemigroup
open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralWrightFisherRaw
open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem
open MathlibExt.Biology.PopulationGenetics.Diffusion.SelectionMonotoneClass

/-! ### Non-vacuity with a nonzero selection coefficient, computed from the definitions

At the boundary state `0` the selection generator `L_σ f (0) = 0` vanishes for every `σ`, so the
process frozen at `0` solves the selection martingale problem with `σ = 1`, and it is Markov for
the identity kernels. This instance is degenerate: nothing ties `κ` to the selection dynamics in
the interior of `[0, 1]`, and it is the only `σ ≠ 0` instance available. -/

/-- The identity kernels at every time. -/
noncomputable def idFamily : ℝ≥0 → Kernel I I := fun _ => Kernel.id

instance (t : ℝ≥0) : IsMarkovKernel (idFamily t) := by
  unfold idFamily
  infer_instance

theorem idFamily_add (s t : ℝ≥0) : idFamily (s + t) = idFamily t ∘ₖ idFamily s := by
  simp [idFamily]

theorem integral_idFamily (t : ℝ≥0) (g : I → ℝ) (x : I) : ∫ y, g y ∂idFamily t x = g x := by
  rw [idFamily, Kernel.id_apply, integral_dirac]

theorem isFellerFamily_idFamily : IsFellerFamily idFamily := fun t g => by
  simp only [integral_idFamily]
  exact g.continuous

private theorem projIcc_zero : projIcc (0 : ℝ) 1 zero_le_one 0 = 0 := projIcc_left _

/-- The frozen process at `0` is a Wright–Fisher diffusion with selection `σ = 1`, Markov for
the identity kernels. -/
theorem isSelectionMarkov_const_zero {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    IsSelectionMarkov 1 idFamily ℱ μ fun _ _ => (0 : ℝ) where
  solution := by
    refine ⟨fun _ _ => by simp, fun _ => continuous_const, fun _ => stronglyMeasurable_const,
      fun f _ => ?_⟩
    simpa [MathlibExt.Biology.PopulationGenetics.Diffusion.generator] using
      martingale_const ℱ μ (0 : ℝ)
  markov s t _ g := by
    rw [condExp_const (ℱ.le s)]
    exact Eventually.of_forall fun _ => (integral_idFamily _ g _).symm

-- The whole-path strong Markov theorem applies with `σ = 1` at every stopping time.
example {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ≥0 mΩ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    {F : SamplePath → ℝ} (hF : Measurable F) {C : ℝ} (hFC : ∀ y, ‖F y‖ ≤ C) :
    μ[{ω | τ ω ≠ ⊤}.indicator (fun ω => F fun u => projIcc (0 : ℝ) 1 zero_le_one
        (stoppedValue (fun (_ : ℝ≥0) (_ : Ω) => (0 : ℝ)) (fun ω => τ ω + u) ω)) |
        hτ.measurableSpace] =ᵐ[μ]
      {ω | τ ω ≠ ⊤}.indicator (fun ω => ∫ y, F y ∂pathMeasure idFamily idFamily_add
        (projIcc (0 : ℝ) 1 zero_le_one (stoppedValue (fun (_ : ℝ≥0) (_ : Ω) => (0 : ℝ)) τ ω))) :=
  (isSelectionMarkov_const_zero ℱ μ).condExp_indicator_path_stoppedValue_add
    isFellerFamily_idFamily idFamily_add hτ hF hFC

-- The bounded-measurable statement with `σ = 1`, for the indicator of `{0}`; by
-- `integral_idFamily` its right side is `1_{τ < ∞}` (computed from the definitions).
example {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ≥0 mΩ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) (t : ℝ≥0) :
    μ[{ω | τ ω ≠ ⊤}.indicator (fun ω => ({0} : Set I).indicator (fun _ => (1 : ℝ))
        (projIcc (0 : ℝ) 1 zero_le_one
          (stoppedValue (fun (_ : ℝ≥0) (_ : Ω) => (0 : ℝ)) (fun ω => τ ω + t) ω))) |
        hτ.measurableSpace] =ᵐ[μ]
      {ω | τ ω ≠ ⊤}.indicator (fun _ => (1 : ℝ)) := by
  refine ((isSelectionMarkov_const_zero ℱ μ).condExp_indicator_comp_stoppedValue_add
    isFellerFamily_idFamily hτ t (measurable_const.indicator (measurableSet_singleton 0))
    (C := 1) (fun _ => (norm_indicator_le_norm_self _ _).trans (by simp))).trans ?_
  refine Eventually.of_forall fun ω => ?_
  simp only [integral_idFamily, stoppedValue, projIcc_zero,
    Set.indicator_of_mem (Set.mem_singleton (0 : I))]

/-! ### The Feller hypothesis is not automatic -/

/-- Rounding to `0` below `1/2` and to `1` from `1/2` on. -/
noncomputable def roundI (x : I) : I := if (x : ℝ) < 1 / 2 then 0 else 1

theorem measurable_roundI : Measurable roundI :=
  Measurable.ite (measurableSet_lt measurable_subtype_coe measurable_const) measurable_const
    measurable_const

-- The deterministic kernels of a discontinuous map are not Feller: the integral of the identity
-- would be a continuous function on the connected space `[0, 1]` taking only the values `0` and
-- `1`, and both of them.
example : ¬ IsFellerFamily fun _ => Kernel.deterministic roundI measurable_roundI := by
  intro h
  have hc := h 0 ⟨Subtype.val, continuous_subtype_val⟩
  have hval : ∀ x : I, ∫ y, (⟨Subtype.val, continuous_subtype_val⟩ : C(I, ℝ)) y
      ∂Kernel.deterministic roundI measurable_roundI x = (roundI x : ℝ) := fun x => by
    rw [Kernel.deterministic_apply, integral_dirac]
    rfl
  simp only [hval] at hc
  have h0 : ((roundI 0 : I) : ℝ) = 0 := by norm_num [roundI]
  have h1 : ((roundI 1 : I) : ℝ) = 1 := by norm_num [roundI]
  obtain ⟨x, hx⟩ := intermediate_value_univ (0 : I) 1 hc
    (show (1 / 2 : ℝ) ∈ Icc ((roundI 0 : I) : ℝ) ((roundI 1 : I) : ℝ) by
      rw [h0, h1]
      constructor <;> norm_num)
  simp only [roundI] at hx
  split_ifs at hx <;> norm_num at hx

/-! ### The neutral case -/

-- The canonical path measure of `neutralKernel` is the neutral `rawMeasure`.
example (x : I) : pathMeasure neutralKernel neutralKernel_add x = rawMeasure x := rfl

-- The indicator of `[0, 1/2)` is bounded and measurable but not continuous; the strong Markov
-- property holds for it at every stopping time of the neutral realization, through the
-- selection theorem at `σ = 0`.
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
  (isSelectionMarkov_zero_modifiedProcess x).condExp_indicator_comp_stoppedValue_add
    isFellerFamily_neutralKernel hτ t (measurable_const.indicator measurableSet_Iio) (C := 1)
    (fun _ => (norm_indicator_le_norm_self _ _).trans (by simp))

-- Two-time functional of the neutral realization at a stopping time.
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
  (isSelectionMarkov_zero_modifiedProcess x).condExp_indicator_finite_stoppedValue_add
    isFellerFamily_neutralKernel hτ (t := ![1, 2])
    (fun i j hij => by fin_cases i <;> fin_cases j <;> simp_all)
    (measurable_const.indicator (measurableSet_le (measurable_pi_apply 0) (measurable_pi_apply 1)))
    (C := 1) (fun _ => (norm_indicator_le_norm_self _ _).trans (by simp))

-- The deterministic-time path statement uses no Feller hypothesis.
example (x : I) (s : ℝ≥0) {F : SamplePath → ℝ} (hF : Measurable F) {C : ℝ}
    (hFC : ∀ y, ‖F y‖ ≤ C) :
    (rawMeasure x)[fun ω => F fun u => projIcc (0 : ℝ) 1 zero_le_one (modifiedProcess x (s + u) ω) |
        naturalFiltration x s] =ᵐ[rawMeasure x]
      fun ω => ∫ y, F y ∂rawMeasure (projIcc (0 : ℝ) 1 zero_le_one (modifiedProcess x s ω)) :=
  (isSelectionMarkov_zero_modifiedProcess x).condExp_path_add neutralKernel_add s hF hFC

/-! ### Boundary cases, computed from the definitions -/

section Boundary

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ}

-- The stopping time that never stops: both sides vanish identically.
example (F : SamplePath → ℝ) :
    let hτ : IsStoppingTime ℱ fun _ : Ω => (⊤ : WithTop ℝ≥0) := fun i => by simp
    μ[{_ω | (⊤ : WithTop ℝ≥0) ≠ ⊤}.indicator (fun ω => F fun u => projIcc (0 : ℝ) 1 zero_le_one
        (stoppedValue X (fun _ => (⊤ : WithTop ℝ≥0) + u) ω)) | hτ.measurableSpace] =
      {_ω | (⊤ : WithTop ℝ≥0) ≠ ⊤}.indicator (fun ω => ∫ y, F y ∂pathMeasure idFamily
        idFamily_add (projIcc (0 : ℝ) 1 zero_le_one
          (stoppedValue X (fun _ => (⊤ : WithTop ℝ≥0)) ω))) := by
  intro hτ
  simp

-- Zero times: the multi-time kernel is the point mass at the empty vector.
example (s : ℝ≥0) (t : Fin 0 → ℝ≥0) (x : I) :
    finiteChainKernel idFamily s t x = Measure.dirac fun i => Fin.elim0 i := by
  rw [finiteChainKernel, Kernel.deterministic_apply]

end Boundary

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.SelectionMonotoneClass
