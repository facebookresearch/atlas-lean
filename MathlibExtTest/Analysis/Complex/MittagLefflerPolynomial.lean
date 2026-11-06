/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.LinearCombination
import MathlibExt.Analysis.Complex.MittagLefflerPolynomial

set_option autoImplicit false

open Filter Polynomial Set Topology

-- A simple pole with residue `1` at every natural number: `b ν = ν` and `P ν = X`.
example : ∃ f : ℂ → ℂ, Meromorphic f ∧ (∀ z ∉ range ((↑) : ℕ → ℂ), AnalyticAt ℂ f z) ∧
    ∀ ν : ℕ, ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ ν ∧ ∀ᶠ z in 𝓝[≠] (ν : ℂ), f z = (z - ν)⁻¹ + φ z := by
  simpa only [eval_X] using (Complex.mittag_leffler_of_coeff_zero_eq_zero
    (b := ((↑) : ℕ → ℂ)) Nat.cast_injective
    (by simpa only [Complex.norm_natCast] using tendsto_natCast_atTop_atTop (R := ℝ))
    (fun _ ↦ X) fun _ ↦ coeff_X_zero).1

-- The entire part is free: adding a constant to a solution prescribes its value at a point.
-- This uses both directions of the `↔`.
example {b : ℕ → ℂ} (hb_inj : Function.Injective b) (hb : Tendsto (fun ν ↦ ‖b ν‖) atTop atTop)
    (P : ℕ → ℂ[X]) (z₀ w : ℂ) :
    ∃ f : ℂ → ℂ, f z₀ = w ∧ Meromorphic f ∧ (∀ z ∉ range b, AnalyticAt ℂ f z) ∧
      ∀ ν, ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ (b ν) ∧
        ∀ᶠ z in 𝓝[≠] b ν, f z = (P ν).eval (z - b ν)⁻¹ + φ z := by
  obtain ⟨⟨f, hf⟩, p, hp⟩ := Complex.mittag_leffler hb_inj hb P
  obtain ⟨g, hg, hfg⟩ := (hp f).1 hf
  refine ⟨fun z ↦ f z + (w - f z₀), by simp,
    (hp _).2 ⟨fun z ↦ g z + (w - f z₀), hg.add_const _, fun z hz ↦ ?_⟩⟩
  convert hfg z hz using 1
  ring

-- Two functions with the same poles and singular parts differ, off the poles, by an entire
-- function.
example {b : ℕ → ℂ} (hb_inj : Function.Injective b) (hb : Tendsto (fun ν ↦ ‖b ν‖) atTop atTop)
    (P : ℕ → ℂ[X]) {f₁ f₂ : ℂ → ℂ}
    (h₁ : Meromorphic f₁ ∧ (∀ z ∉ range b, AnalyticAt ℂ f₁ z) ∧
      ∀ ν, ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ (b ν) ∧
        ∀ᶠ z in 𝓝[≠] b ν, f₁ z = (P ν).eval (z - b ν)⁻¹ + φ z)
    (h₂ : Meromorphic f₂ ∧ (∀ z ∉ range b, AnalyticAt ℂ f₂ z) ∧
      ∀ ν, ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ (b ν) ∧
        ∀ᶠ z in 𝓝[≠] b ν, f₂ z = (P ν).eval (z - b ν)⁻¹ + φ z) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z ∉ range b, f₁ z = f₂ z + g z := by
  obtain ⟨-, p, hp⟩ := Complex.mittag_leffler hb_inj hb P
  obtain ⟨g₁, hg₁, hf₁⟩ := (hp f₁).1 h₁
  obtain ⟨g₂, hg₂, hf₂⟩ := (hp f₂).1 h₂
  refine ⟨g₁ - g₂, hg₁.sub hg₂, fun z hz ↦ ?_⟩
  rw [Pi.sub_apply]
  linear_combination (hf₁ z hz).unique (hf₂ z hz)

#print axioms Complex.mittag_leffler
#print axioms Complex.mittag_leffler_of_coeff_zero_eq_zero
