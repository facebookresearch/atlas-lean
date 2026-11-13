/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralStrongMarkov

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal unitInterval

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.NeutralStrongMarkov

open MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisherSemigroup
open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralWrightFisherRaw
open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem
open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralStrongMarkov

/-! ### Non-vacuity of the Markov hypothesis -/

-- From the absorbing state `0` the semigroup stays at `0`, computed from the kernel:
-- `P_u g 0 = ∫ g d(K_u 0)` and `K_u 0 = δ₀`.
private theorem wfSemigroup_apply_zero {u : ℝ} (hu : 0 ≤ u) (g : C(I, ℝ)) :
    wfSemigroup u g 0 = g 0 := by
  have h := integral_wfTransitionKernel u g 0
  have hk : wfTransitionKernel u 0 = Measure.dirac 0 := neutralKernel_apply_zero_state ⟨u, hu⟩
  rw [hk, integral_dirac] at h
  exact h.symm

private theorem projIcc_zero : projIcc (0 : ℝ) 1 zero_le_one 0 = 0 := projIcc_left _

-- The constant process at `0` satisfies the Markov hypothesis for every filtration, so the
-- general theorems are not vacuous.
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

-- The general strong Markov property applies to the constant process at every stopping time.
example {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ≥0 mΩ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) (t : ℝ≥0)
    (g : C(I, ℝ)) :
    μ[{ω | τ ω ≠ ⊤}.indicator (fun ω => g (projIcc (0 : ℝ) 1 zero_le_one
        (stoppedValue (fun (_ : ℝ≥0) (_ : Ω) => (0 : ℝ)) (fun ω => τ ω + t) ω))) |
        hτ.measurableSpace] =ᵐ[μ]
      {ω | τ ω ≠ ⊤}.indicator (fun ω => wfSemigroup t g (projIcc (0 : ℝ) 1 zero_le_one
        (stoppedValue (fun (_ : ℝ≥0) (_ : Ω) => (0 : ℝ)) τ ω))) :=
  condExp_stoppedValue_add_ae_eq (fun _ => continuous_const) (fun _ => stronglyMeasurable_const)
    (markov_const_zero ℱ μ) hτ t g

-- The realization started at `0` satisfies the Markov hypothesis of the realization corollary,
-- computed from the absorbing-path lemma `ae_forall_modifiedProcess_zero` (not from the open
-- Markov development).
private theorem markov_modifiedProcess_zero :
    ∀ s t : ℝ≥0, s ≤ t → ∀ g : C(I, ℝ),
      (rawMeasure 0)[fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (modifiedProcess 0 t ω)) |
          naturalFiltration 0 s] =ᵐ[rawMeasure 0]
        fun ω =>
          wfSemigroup ((t : ℝ) - s) g (projIcc (0 : ℝ) 1 zero_le_one (modifiedProcess 0 s ω)) := by
  intro s t hst g
  have hae := ae_forall_modifiedProcess_zero
  have hf : (fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (modifiedProcess 0 t ω))) =ᵐ[rawMeasure 0]
      fun _ => g (projIcc (0 : ℝ) 1 zero_le_one 0) :=
    hae.mono fun ω hω => by simp only [hω t]
  refine (condExp_congr_ae hf).trans ?_
  rw [condExp_const ((naturalFiltration 0).le s)]
  filter_upwards [hae] with ω hω
  rw [hω s, projIcc_zero, wfSemigroup_apply_zero (sub_nonneg.2 (NNReal.coe_le_coe.2 hst))]

-- Hence the realization corollary applies, here at an arbitrary stopping time of the natural
-- filtration and at the deterministic time `1`.
example {τ : SamplePath → WithTop ℝ≥0} (hτ : IsStoppingTime (naturalFiltration 0) τ) (t : ℝ≥0)
    (g : C(I, ℝ)) :
    (rawMeasure 0)[{ω | τ ω ≠ ⊤}.indicator
        (fun ω => g (stoppedValue (modifiedState 0) (fun ω => τ ω + t) ω)) |
        hτ.measurableSpace] =ᵐ[rawMeasure 0]
      {ω | τ ω ≠ ⊤}.indicator (fun ω => wfSemigroup t g (stoppedValue (modifiedState 0) τ ω)) :=
  condExp_modifiedProcess_stoppedValue_add 0 markov_modifiedProcess_zero hτ t g

example (t : ℝ≥0) (g : C(I, ℝ)) :
    (rawMeasure 0)[{_ω | ((1 : ℝ≥0) : WithTop ℝ≥0) ≠ ⊤}.indicator
        (fun ω => g (stoppedValue (modifiedState 0) (fun _ => ((1 : ℝ≥0) : WithTop ℝ≥0) + t) ω)) |
        (isStoppingTime_const (naturalFiltration 0) 1).measurableSpace] =ᵐ[rawMeasure 0]
      {_ω | ((1 : ℝ≥0) : WithTop ℝ≥0) ≠ ⊤}.indicator
        (fun ω => wfSemigroup t g
          (stoppedValue (modifiedState 0) (fun _ => ((1 : ℝ≥0) : WithTop ℝ≥0)) ω)) :=
  condExp_modifiedProcess_stoppedValue_add 0 markov_modifiedProcess_zero
    (isStoppingTime_const _ 1) t g

/-! ### Boundary cases, computed from the definitions -/

section Boundary

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ}

-- Time shift `t = 0`: `P_0 = id` and `1_{τ < ∞} g (X τ)` is `ℱ_τ`-measurable, so the identity
-- holds (even everywhere) without any Markov hypothesis. Proved directly, not through the
-- theorem.
example [IsFiniteMeasure μ] (hcont : ∀ ω, Continuous fun t => X t ω)
    (hadapt : StronglyAdapted ℱ X) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    (g : C(I, ℝ)) :
    μ[{ω | τ ω ≠ ⊤}.indicator (fun ω => g (projIcc (0 : ℝ) 1 zero_le_one
        (stoppedValue X (fun ω => τ ω + (0 : ℝ≥0)) ω))) | hτ.measurableSpace] =
      {ω | τ ω ≠ ⊤}.indicator (fun ω => wfSemigroup ((0 : ℝ≥0) : ℝ) g
        (projIcc (0 : ℝ) 1 zero_le_one (stoppedValue X τ ω))) := by
  have hfin : MeasurableSet[hτ.measurableSpace] {ω | τ ω ≠ ⊤} :=
    hτ.measurable (measurableSet_singleton ⊤).compl
  have hsm : StronglyMeasurable[hτ.measurableSpace] ({ω | τ ω ≠ ⊤}.indicator
      fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (stoppedValue X τ ω))) :=
    (((g.continuous.comp continuous_projIcc).measurable.comp
      (measurable_stoppedValue (hadapt.isStronglyProgressive_of_continuous hcont)
        hτ)).stronglyMeasurable).indicator hfin
  have hint : Integrable ({ω | τ ω ≠ ⊤}.indicator
      fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (stoppedValue X τ ω))) μ :=
    Integrable.of_bound (hsm.mono hτ.measurableSpace_le).aestronglyMeasurable ‖g‖
      (Eventually.of_forall fun _ => (norm_indicator_le_norm_self _ _).trans
        (g.norm_coe_le_norm _))
  simp only [WithTop.coe_zero, add_zero, NNReal.coe_zero, wfSemigroup_zero,
    one_apply_eq_self]
  exact condExp_of_stronglyMeasurable hτ.measurableSpace_le hsm hint

-- The stopping time that never stops: both sides vanish identically.
example (g : C(I, ℝ)) (t : ℝ≥0) :
    let hτ : IsStoppingTime ℱ fun _ : Ω => (⊤ : WithTop ℝ≥0) := fun i => by simp
    μ[{_ω | (⊤ : WithTop ℝ≥0) ≠ ⊤}.indicator (fun ω => g (projIcc (0 : ℝ) 1 zero_le_one
        (stoppedValue X (fun _ => (⊤ : WithTop ℝ≥0) + t) ω))) | hτ.measurableSpace] =
      {_ω | (⊤ : WithTop ℝ≥0) ≠ ⊤}.indicator (fun ω => wfSemigroup t g
        (projIcc (0 : ℝ) 1 zero_le_one (stoppedValue X (fun _ => (⊤ : WithTop ℝ≥0)) ω))) := by
  intro hτ
  simp

-- A deterministic stopping time `τ ≡ s` recovers the simple Markov property between `s` and
-- `s + t`: `ℱ_τ = ℱ s` and `X τ = X s` by definition.
example [IsFiniteMeasure μ] (hcont : ∀ ω, Continuous fun t => X t ω)
    (hadapt : StronglyAdapted ℱ X)
    (hmarkov : ∀ s t : ℝ≥0, s ≤ t → ∀ g : C(I, ℝ),
      μ[fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (X t ω)) | ℱ s] =ᵐ[μ]
        fun ω => wfSemigroup ((t : ℝ) - s) g (projIcc (0 : ℝ) 1 zero_le_one (X s ω)))
    (s t : ℝ≥0) (g : C(I, ℝ)) :
    μ[fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (X (s + t) ω)) | ℱ s] =ᵐ[μ]
      fun ω => wfSemigroup t g (projIcc (0 : ℝ) 1 zero_le_one (X s ω)) := by
  have h := condExp_stoppedValue_add_ae_eq_of_ne_top hcont hadapt hmarkov
    (isStoppingTime_const ℱ s) (fun _ => WithTop.coe_ne_top) t g
  have hsv : ∀ ω, stoppedValue X (fun _ => (s : WithTop ℝ≥0) + t) ω = X (s + t) ω := fun ω => by
    simp only [stoppedValue, ← WithTop.coe_add]
    exact congrArg (X · ω) (WithTop.untopD_coe _ _)
  simp only [hsv, IsStoppingTime.measurableSpace_const, stoppedValue_const] at h
  exact h

end Boundary

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.NeutralStrongMarkov
