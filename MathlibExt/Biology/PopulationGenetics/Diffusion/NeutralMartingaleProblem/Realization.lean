/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Process.Adapted
public import MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralWrightFisherRaw

/-!
# The neutral Wright--Fisher realization with its natural filtration

`NeutralWrightFisherRaw.continuousRealization x` selects, for every initial
frequency `x ∈ [0, 1]`, a continuous `[0, 1]`-valued modification
`modifiedProcess x` of the canonical coordinate process under the path measure
`rawMeasure x` built from the neutral transition kernels `neutralKernel t`.
This file attaches a filtration to that realization and records how it is tied
to the existing kernel and semigroup.  No second realization is constructed.

## Main definitions

* `modifiedState x t`: the selected process viewed in the state space `I`.
* `naturalFiltration x`: the natural filtration of `modifiedProcess x`.

## Main results

* `stronglyAdapted_naturalFiltration`: the realization is adapted to it.
* `map_modifiedState`, `map_modifiedState_pair_of_lt`: one- and two-time laws
  are given by the neutral transition kernel.
* `integral_modifiedState`: `E_x[f (X_t)] = wfSemigroup t f x` for continuous
  `f`; `integral_modifiedProcess`: `E_x[X_t] = x`.
* `neutralKernel_apply_zero_state`, `neutralKernel_apply_one_state`: the
  boundary states are absorbing for the kernel.
* `ae_forall_modifiedProcess_zero`, `ae_forall_modifiedProcess_one`: started
  at `0` (resp. `1`), almost every path is identically `0` (resp. `1`).

The Markov property with respect to `naturalFiltration` and the martingale
problem are not proved here.

## References

* S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and
  Convergence*, Wiley (1986), ch. 2 (filtrations, adaptedness) and ch. 4, 10.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory unitInterval

namespace MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem

open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralWrightFisherRaw
open MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisherSemigroup
open MathlibExt.Biology.PopulationGenetics.Coalescent.KingmanBlockCounting

noncomputable section

/-! ### Kernel facts -/

/-- The neutral kernel preserves the mean: `∫ y dK_t(x, y) = x`. -/
theorem integral_neutralKernel_coe (t : NNReal) (x : I) :
    ∫ y, (y : ℝ) ∂neutralKernel t x = x := by
  have hG : blockCountingGenerator 1 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blockCountingGenerator]
  have h := integral_wfTransitionKernel_X_pow t.coe_nonneg 1 x
  simp only [hG, smul_zero, NormedSpace.exp_zero] at h
  simpa [neutralKernel, Fin.sum_univ_two, Matrix.one_apply] using h

/-- A probability measure on `[0, 1]` with mean `0` is the point mass at `0`. -/
private theorem eq_dirac_zero_of_integral_eq_zero {ν : Measure I} [IsProbabilityMeasure ν]
    (h : ∫ y, (y : ℝ) ∂ν = 0) : ν = Measure.dirac 0 := by
  have hint : Integrable (fun y : I => (y : ℝ)) ν :=
    (integrable_const (1 : ℝ)).mono' (by fun_prop) (Filter.Eventually.of_forall fun y => by
      simpa [abs_of_nonneg y.2.1] using y.2.2)
  have hae : (fun y : I => (y : ℝ)) =ᵐ[ν] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun y => y.2.1) hint).1 h
  have hid : (id : I → I) =ᵐ[ν] fun _ => 0 := by
    filter_upwards [hae] with y hy
    exact Subtype.ext hy
  simpa using (hasLaw_dirac_of_ae_eq hid).map_eq

/-- The boundary state `0` is absorbing for the neutral kernel. -/
theorem neutralKernel_apply_zero_state (t : NNReal) :
    neutralKernel t 0 = Measure.dirac 0 :=
  eq_dirac_zero_of_integral_eq_zero (by simpa using integral_neutralKernel_coe t 0)

/-- The boundary state `1` is absorbing for the neutral kernel. -/
theorem neutralKernel_apply_one_state (t : NNReal) :
    neutralKernel t 1 = Measure.dirac 1 := by
  set ν := neutralKernel t 1
  have h1 : ∫ y, (y : ℝ) ∂ν = 1 := by simpa using integral_neutralKernel_coe t 1
  have hσ : ν.map unitInterval.symm = Measure.dirac 0 := by
    apply eq_dirac_zero_of_integral_eq_zero
    rw [integral_map (by fun_prop) (by fun_prop)]
    simp only [unitInterval.coe_symm_eq]
    rw [integral_sub (integrable_const _) ?_, h1]
    · simp
    · exact (integrable_const (1 : ℝ)).mono' (by fun_prop)
        (Filter.Eventually.of_forall fun y => by simpa [abs_of_nonneg y.2.1] using y.2.2)
  have hm : Measurable unitInterval.symm := unitInterval.continuous_symm.measurable
  have hνν : ν = (ν.map unitInterval.symm).map unitInterval.symm := by
    rw [Measure.map_map hm hm, unitInterval.symm_involutive.comp_self, Measure.map_id]
  rw [hνν, hσ, Measure.map_dirac' hm, unitInterval.symm_zero]

/-! ### The realization as a state-valued process -/

/-- The selected continuous realization `modifiedProcess x` viewed as a process
with values in the state space `I = [0, 1]`. -/
noncomputable def modifiedState (x : I) (t : NNReal) (ω : SamplePath) : I :=
  ⟨modifiedProcess x t ω, modifiedProcess_mem_Icc x t ω⟩

@[simp]
theorem coe_modifiedState (x : I) (t : NNReal) (ω : SamplePath) :
    (modifiedState x t ω : ℝ) = modifiedProcess x t ω :=
  rfl

theorem measurable_modifiedState (x : I) (t : NNReal) :
    Measurable (modifiedState x t) :=
  (measurable_modifiedProcess x t).subtype_mk

theorem continuous_modifiedState (x : I) (ω : SamplePath) :
    Continuous fun t => modifiedState x t ω :=
  (continuous_modifiedProcess x ω).subtype_mk _

@[simp]
theorem modifiedState_zero (x : I) (ω : SamplePath) : modifiedState x 0 ω = x :=
  Subtype.ext (modifiedProcess_zero x ω)

/-- At each fixed time the realization agrees almost surely with the canonical
coordinate. -/
theorem modifiedState_ae_eq_eval (x : I) (t : NNReal) :
    modifiedState x t =ᵐ[rawMeasure x] fun ω => ω t := by
  filter_upwards [modifiedProcess_ae_eq_raw x t, rawProcess_ae_eq_coordinate x t]
    with ω hmod hraw
  exact Subtype.ext (hmod.trans hraw)

/-! ### Laws of the realization -/

/-- The one-time law of the realization is the neutral transition kernel. -/
theorem map_modifiedState (x : I) (t : NNReal) :
    (rawMeasure x).map (modifiedState x t) = neutralKernel t x := by
  rw [Measure.map_congr (modifiedState_ae_eq_eval x t), map_eval_rawMeasure]

/-- The real-valued one-time law of the realization. -/
theorem map_modifiedProcess (x : I) (t : NNReal) :
    (rawMeasure x).map (modifiedProcess x t) =
      (neutralKernel t x).map ((↑) : I → ℝ) := by
  rw [← map_modifiedState, Measure.map_map measurable_subtype_coe
    (measurable_modifiedState x t)]
  rfl

/-- The ordered two-time law of the realization is the first marginal followed
by the neutral transition over the time gap. -/
theorem map_modifiedState_pair_of_lt (x : I) {s t : NNReal} (hst : s < t) :
    (rawMeasure x).map (fun ω => (modifiedState x s ω, modifiedState x t ω)) =
      (neutralKernel s x) ⊗ₘ neutralKernel (t - s) := by
  rw [← map_pair_rawMeasure_of_lt x hst]
  apply Measure.map_congr
  filter_upwards [modifiedState_ae_eq_eval x s, modifiedState_ae_eq_eval x t]
    with ω hs ht
  rw [hs, ht]

/-- Semigroup form of the one-time law: `E_x[f (X_t)] = (P_t f)(x)` for every
continuous test function `f` on `[0, 1]`. -/
theorem integral_modifiedState (x : I) (t : NNReal) (f : C(I, ℝ)) :
    ∫ ω, f (modifiedState x t ω) ∂rawMeasure x = wfSemigroup t f x := by
  rw [← integral_map (measurable_modifiedState x t).aemeasurable
    f.continuous.aestronglyMeasurable, map_modifiedState]
  exact integral_wfTransitionKernel _ f x

/-- The realization has constant mean: `E_x[X_t] = x`. -/
theorem integral_modifiedProcess (x : I) (t : NNReal) :
    ∫ ω, modifiedProcess x t ω ∂rawMeasure x = x := by
  rw [← integral_neutralKernel_coe t x, ← map_modifiedState,
    integral_map (measurable_modifiedState x t).aemeasurable (by fun_prop)]
  rfl

/-! ### The natural filtration -/

/-- The natural filtration of the selected continuous realization: at time `t`
it is generated by `modifiedProcess x s` for `s ≤ t`. -/
noncomputable def naturalFiltration (x : I) :
    Filtration NNReal (inferInstance : MeasurableSpace SamplePath) :=
  Filtration.natural (modifiedProcess x)
    fun t => (measurable_modifiedProcess x t).stronglyMeasurable

/-- The realization is adapted to its natural filtration. -/
theorem stronglyAdapted_naturalFiltration (x : I) :
    StronglyAdapted (naturalFiltration x) (modifiedProcess x) :=
  Filtration.stronglyAdapted_natural _

/-- Each past value is measurable for the natural filtration at a later time. -/
theorem measurable_modifiedProcess_naturalFiltration (x : I) {s t : NNReal}
    (hst : s ≤ t) :
    Measurable[naturalFiltration x t] (modifiedProcess x s) :=
  ((stronglyAdapted_naturalFiltration x s).mono
    ((naturalFiltration x).mono hst)).measurable

/-! ### Absorbing initial states -/

/-- Fixed-time almost-sure constancy upgrades to pathwise constancy for the
continuous realization, using a countable dense set of times. -/
private theorem ae_forall_of_forall_ae (x : I) (c : ℝ)
    (h : ∀ t, ∀ᵐ ω ∂rawMeasure x, modifiedProcess x t ω = c) :
    ∀ᵐ ω ∂rawMeasure x, ∀ t, modifiedProcess x t ω = c := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense NNReal
  have := hDc.to_subtype
  have hD : ∀ᵐ ω ∂rawMeasure x, ∀ t : D, modifiedProcess x t ω = c :=
    ae_all_iff.2 fun t => h t
  filter_upwards [hD] with ω hω t
  have := Continuous.ext_on hDd (continuous_modifiedProcess x ω) continuous_const
    (fun s hs => hω ⟨s, hs⟩)
  exact congrFun this t

/-- Started at `0`, almost every path of the realization is identically `0`. -/
theorem ae_forall_modifiedProcess_zero :
    ∀ᵐ ω ∂rawMeasure 0, ∀ t, modifiedProcess 0 t ω = 0 := by
  refine ae_forall_of_forall_ae 0 0 fun t => ?_
  have h : ∀ᵐ y ∂(rawMeasure 0).map (modifiedState 0 t), y = (0 : I) := by
    rw [map_modifiedState, neutralKernel_apply_zero_state]
    exact (ae_dirac_iff (measurableSet_singleton 0)).2 rfl
  filter_upwards [ae_of_ae_map (measurable_modifiedState 0 t).aemeasurable h] with ω hω
  exact congrArg Subtype.val hω

/-- Started at `1`, almost every path of the realization is identically `1`. -/
theorem ae_forall_modifiedProcess_one :
    ∀ᵐ ω ∂rawMeasure 1, ∀ t, modifiedProcess 1 t ω = 1 := by
  refine ae_forall_of_forall_ae 1 1 fun t => ?_
  have h : ∀ᵐ y ∂(rawMeasure 1).map (modifiedState 1 t), y = (1 : I) := by
    rw [map_modifiedState, neutralKernel_apply_one_state]
    exact (ae_dirac_iff (measurableSet_singleton 1)).2 rfl
  filter_upwards [ae_of_ae_map (measurable_modifiedState 1 t).aemeasurable h] with ω hω
  exact congrArg Subtype.val hω

end

end MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem
