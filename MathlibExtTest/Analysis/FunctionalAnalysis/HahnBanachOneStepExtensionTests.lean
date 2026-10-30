/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.FunctionalAnalysis.HahnBanachOneStepExtension
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Tests for the one-step Hahn–Banach extension

* On `ℝ × ℝ`, with `M = span {(1, 0)}` and `f` the restriction of the first
  coordinate functional: the extension `g` to `M ⊔ ℝ ∙ (0, 1)` satisfies
  `g (1, 0) = 1` (it extends `f`), obeys the bound `‖g v‖ ≤ ‖v‖` for all
  `v`, and `M` is strictly
  smaller than the extended subspace.
* The degenerate case `M = ⊥`, `f = 0`, `C = 0` over `ℂ`: the bound
  forces the extension to vanish, and `⊥ < ⊥ ⊔ ℂ ∙ 1`.
-/

namespace MathlibExtTest.Analysis.FunctionalAnalysis.HahnBanachOneStepExtensionTests

open MathlibExt.Analysis.FunctionalAnalysis.HahnBanachOneStepExtension
open Submodule

/-- The one-step extension on `ℝ × ℝ`: extension property, bound, strictness. -/
example :
    ∃ g : ↥(span ℝ {((1, 0) : ℝ × ℝ)} ⊔ ℝ ∙ ((0, 1) : ℝ × ℝ)) →L[ℝ] ℝ,
      g ⟨((1, 0) : ℝ × ℝ), Submodule.mem_sup_left
        (Submodule.mem_span_singleton_self ((1, 0) : ℝ × ℝ))⟩ = 1 ∧
      (∀ v : ↥(span ℝ {((1, 0) : ℝ × ℝ)} ⊔ ℝ ∙ ((0, 1) : ℝ × ℝ)),
        ‖g v‖ ≤ 1 * ‖(v : ℝ × ℝ)‖) ∧
      span ℝ {((1, 0) : ℝ × ℝ)} < span ℝ {((1, 0) : ℝ × ℝ)} ⊔ ℝ ∙ ((0, 1) : ℝ × ℝ) := by
  have hf_bound : ∀ m : ↥(span ℝ {((1, 0) : ℝ × ℝ)}),
      ‖((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
        (span ℝ {((1, 0) : ℝ × ℝ)}).subtypeL) m‖ ≤ (1 : ℝ) * ‖(m : ℝ × ℝ)‖ := by
    intro m
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      ContinuousLinearMap.coe_fst', one_mul]
    rw [Prod.norm_def]
    exact le_max_left _ _
  have hx₀ : ((0, 1) : ℝ × ℝ) ∉ span ℝ {((1, 0) : ℝ × ℝ)} := by
    rw [Submodule.mem_span_singleton]
    rintro ⟨a, ha⟩
    have h1 := congrArg Prod.fst ha
    have h2 := congrArg Prod.snd ha
    simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero] at h1 h2
    norm_num at h2
  obtain ⟨g, hg_ext, hg_bound, hlt⟩ :=
    hahn_banach_one_step_extension_bound (span ℝ {((1, 0) : ℝ × ℝ)})
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (span ℝ {((1, 0) : ℝ × ℝ)}).subtypeL)
      1 (by norm_num) hf_bound ((0, 1) : ℝ × ℝ) hx₀
  refine ⟨g, ?_, ?_, hlt⟩
  · have h_ext := hg_ext ⟨((1, 0) : ℝ × ℝ),
      Submodule.mem_span_singleton_self ((1, 0) : ℝ × ℝ)⟩
    rw [h_ext]
    simp [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  · intro v
    simpa using hg_bound v

/-- The degenerate case over `ℂ`: with `C = 0` and `f = 0`, the extension vanishes. -/
example :
    ∃ g : ↥((⊥ : Submodule ℂ ℂ) ⊔ ℂ ∙ (1 : ℂ)) →L[ℂ] ℂ,
      g ⟨(1 : ℂ), Submodule.mem_sup_right
        (Submodule.mem_span_singleton_self (1 : ℂ))⟩ = 0 ∧
      (⊥ : Submodule ℂ ℂ) < ⊥ ⊔ ℂ ∙ (1 : ℂ) := by
  obtain ⟨g, _hg_ext, hg_bound, hlt⟩ :=
    hahn_banach_one_step_extension_bound (⊥ : Submodule ℂ ℂ)
      (0 : ↥(⊥ : Submodule ℂ ℂ) →L[ℂ] ℂ)
      0 (by norm_num) (fun m => by simp) (1 : ℂ) (by simp)
  refine ⟨g, ?_, hlt⟩
  have h := hg_bound ⟨(1 : ℂ), Submodule.mem_sup_right
    (Submodule.mem_span_singleton_self (1 : ℂ))⟩
  simp only [zero_mul] at h
  exact norm_le_zero_iff.mp h

end MathlibExtTest.Analysis.FunctionalAnalysis.HahnBanachOneStepExtensionTests
