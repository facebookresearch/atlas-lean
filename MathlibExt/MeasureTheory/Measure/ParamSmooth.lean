/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_MeasureTheory_contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport.lean`
and
`P2M/Sol/S_MeasureTheory_contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Smoothness of parameter integrals with compact support

The integral `p ↦ ∫ x, w x • Ψ (c x, p) ∂μ` of a smooth compactly
supported function is smooth in the parameter `p`: differentiation under
the integral sign, iterated over all orders.
-/

@[expose] public section

open MeasureTheory

namespace ParamSmoothAux

universe uM uP uE

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopology X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  {M : Type uM} [NormedAddCommGroup M] [NormedSpace ℝ M]
  {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]

private theorem exists_bound_of_hasCompactSupport {Y E : Type*} [TopologicalSpace Y]
    [NormedAddCommGroup E] {f : Y → E} (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y, ‖f y‖ ≤ B := by
  obtain ⟨B, hB⟩ := hfc.exists_bound_of_continuous hf
  exact ⟨max B 0, le_max_right _ _, fun y => (hB y).trans (le_max_left _ _)⟩

private theorem contDiff_integral_smul_comp (c : X → M) (hc : Continuous c) (w : X → ℝ)
    (hw : Continuous w) (hwc : HasCompactSupport w) (n : ℕ) :
    ∀ {E : Type (max uP uE)} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (Ψ : M × P → E),
      ContDiff ℝ (⊤ : ℕ∞) Ψ → HasCompactSupport Ψ →
        ContDiff ℝ n (fun p : P => ∫ x, w x • Ψ (c x, p) ∂μ) := by
  induction n with
  | zero =>
    intro E _ _ _ Ψ hΨ hΨc
    rw [Nat.cast_zero, contDiff_zero]
    obtain ⟨B, hB0, hB⟩ := exists_bound_of_hasCompactSupport hΨ.continuous hΨc
    have hFc : ∀ p : P, Continuous fun x => w x • Ψ (c x, p) := fun p =>
      hw.smul (hΨ.continuous.comp (hc.prodMk continuous_const))
    refine continuous_of_dominated (bound := fun x => ‖w x‖ * B) ?_ ?_ ?_ ?_
    · exact fun p => (hFc p).aestronglyMeasurable
    · refine fun p => Filter.Eventually.of_forall fun x => ?_
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
    · exact ((continuous_norm.comp hw).mul continuous_const).integrable_of_hasCompactSupport
        ((hwc.norm).mul_right)
    · exact Filter.Eventually.of_forall fun x =>
        (hΨ.continuous.comp (continuous_const.prodMk continuous_id)).const_smul (w x)
  | succ n ih =>
    intro E _ _ _ Ψ hΨ hΨc
    set Ψ' : M × P → (P →L[ℝ] E) := fun q => (fderiv ℝ Ψ q).comp (ContinuousLinearMap.inr ℝ M P)
      with hΨ'_def
    have hfd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ Ψ) := (contDiff_infty_iff_fderiv.mp hΨ).2
    have hΨ's : ContDiff ℝ (⊤ : ℕ∞) Ψ' := hfd.clm_comp contDiff_const
    have hΨ'c : HasCompactSupport Ψ' := by
      refine IsCompact.of_isClosed_subset (hΨc.fderiv (𝕜 := ℝ)) isClosed_closure ?_
      refine closure_mono ?_
      intro q hq
      rw [Function.mem_support] at hq ⊢
      contrapose! hq
      simp [hΨ'_def, hq]
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun p => ∫ x, w x • Ψ' (c x, p) ∂μ, ih Ψ' hΨ's hΨ'c, fun p₀ => ?_⟩
    obtain ⟨B, hB0, hB⟩ := exists_bound_of_hasCompactSupport hΨ's.continuous hΨ'c
    have hFc : ∀ p : P, Continuous fun x => w x • Ψ (c x, p) := fun p =>
      hw.smul (hΨ.continuous.comp (hc.prodMk continuous_const))
    have hF'c : ∀ p : P, Continuous fun x => w x • Ψ' (c x, p) := fun p =>
      hw.smul (hΨ's.continuous.comp (hc.prodMk continuous_const))
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := μ) (s := Set.univ)
      (x₀ := p₀) (F := fun (p : P) (x : X) => w x • Ψ (c x, p))
      (F' := fun (p : P) (x : X) => w x • Ψ' (c x, p)) (bound := fun x => ‖w x‖ * B)
      Filter.univ_mem (Filter.Eventually.of_forall fun p => (hFc p).aestronglyMeasurable) ?_
      (hF'c p₀).aestronglyMeasurable ?_ ?_ ?_
    · exact (hFc p₀).integrable_of_hasCompactSupport (hwc.smul_right)
    · refine Filter.Eventually.of_forall fun x p _ => ?_
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
    · exact ((continuous_norm.comp hw).mul continuous_const).integrable_of_hasCompactSupport
        ((hwc.norm).mul_right)
    · refine Filter.Eventually.of_forall fun x p _ => ?_
      have h1 : HasFDerivAt Ψ (fderiv ℝ Ψ (c x, p)) (c x, p) :=
        (hΨ.differentiable (by simp) (c x, p)).hasFDerivAt
      have h2 : HasFDerivAt (fun p : P => (c x, p)) (ContinuousLinearMap.inr ℝ M P) p :=
        hasFDerivAt_prodMk_right (c x) p
      exact (h1.comp p h2).const_smul (w x)

end ParamSmoothAux

namespace MeasureTheory

universe uX vM vP vE

/-- The integral `p ↦ ∫ x, w x • Ψ (c x, p) ∂μ` of a smooth compactly
supported function is smooth in the parameter `p`. -/
theorem contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport
    {X : Type uX} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [SecondCountableTopology X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    {M : Type vM} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {P : Type vP} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type vE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (c : X → M) (hc : Continuous c) (w : X → ℝ) (hw : Continuous w) (hwc : HasCompactSupport w)
    (Ψ : M × P → E) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨc : HasCompactSupport Ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : P => ∫ x, w x • Ψ (c x, p) ∂μ) := by
  let e : ULift.{max vP vE, vE} E ≃L[ℝ] E := ContinuousLinearEquiv.ulift
  let Ψ' : M × P → ULift.{max vP vE, vE} E := e.symm ∘ Ψ
  have hΨ' : ContDiff ℝ (⊤ : ℕ∞) Ψ' := e.symm.contDiff.comp hΨ
  have hΨ'c : HasCompactSupport Ψ' := by
    simpa only [Ψ'] using hΨc.comp_left e.symm.map_zero
  rw [contDiff_infty]
  intro n
  have hLift := ParamSmoothAux.contDiff_integral_smul_comp.{vM, vP, max vP vE, uX}
    μ c hc w hw hwc n Ψ' hΨ' hΨ'c
  have hDown := e.contDiff.comp hLift
  convert hDown using 1
  funext p
  change (∫ x, w x • Ψ (c x, p) ∂μ) = e (∫ x, w x • Ψ' (c x, p) ∂μ)
  rw [← e.integral_comp_comm]
  simp [Ψ', e]

end MeasureTheory
