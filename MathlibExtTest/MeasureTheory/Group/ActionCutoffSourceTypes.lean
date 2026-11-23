/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Source types are from `anthropics/fermats-last-theorem`, commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`, in `Theorems/`:
* `Thm_MeasureTheory_integrable_and_integral_withDensity_eq_of_forall_lintegral_subgroup_mul_eq_one.lean`
* `Thm_MeasureTheory_lintegral_mul_eq_lintegral_mul_of_forall_lintegral_subgroup_mul_eq_one.lean`
* `Thm_MeasureTheory_lintegral_mul_eq_lintegral_mul_of_forall_mul_eq_of_ae_lintegral_comp_mul_eq_one.lean`
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under Apache 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Source: https://github.com/anthropics/fermats-last-theorem
The upstream NOTICE also credits Mathlib, copyright its respective authors,
released under Apache 2.0: https://github.com/leanprover-community/mathlib4
-/

module

import MathlibExt.MeasureTheory.Group.ActionCutoff
import MathlibExt.MeasureTheory.Group.ActionCutoffWithDensity

/-! # Exact source-type consumers for measurable cutoff transport -/

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace CutoffTransportTest

private theorem invInvariant_of_lintegral {A : Type*} [Group A]
    [MeasurableSpace A] [MeasurableInv A] (τ : Measure A)
    (h : ∀ f : A → ℝ≥0∞, ∫⁻ a, f a⁻¹ ∂τ = ∫⁻ a, f a ∂τ) : τ.IsInvInvariant := by
  constructor
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.inv_def, lintegral_map hf measurable_inv]
  exact h f

/-- Exact source type: no measurability premise on the unweighted Banach-valued function. -/
theorem subgroup_withDensity
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (H : Subgroup G) (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] (μH : Measure H) [SFinite μH]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hinv : ∀ f : H → ℝ≥0∞, ∫⁻ n, f n⁻¹ ∂μH = ∫⁻ n, f n ∂μH)
    {ρ ρ' : G → ℝ≥0∞} (hρ : Measurable ρ) (hρ' : Measurable ρ')
    (hρ1 : ∀ g, ∫⁻ n : H, ρ ((n : G) * g) ∂μH = 1) (hρ'1 : ∀ g, ∫⁻ n : H, ρ' ((n : G) * g) ∂μH = 1)
    (hρt : ∀ g, ρ g ≠ ∞) (hρ't : ∀ g, ρ' g ≠ ∞)
    {f : G → E} (hfinv : ∀ (n : H) (g : G), f ((n : G) * g) = f g)
    (hfi : Integrable f (μ.withDensity ρ)) :
    Integrable f (μ.withDensity ρ') ∧
      ∫ g, f g ∂μ.withDensity ρ' = ∫ g, f g ∂μ.withDensity ρ := by
  let : MeasurableInv H := ⟨measurable_subtype_coe.inv.subtype_mk⟩
  let := invInvariant_of_lintegral μH hinv
  exact integrable_and_integral_withDensity_eq_of_normalized_smul μH μ
    ((measurable_subtype_coe.comp measurable_fst).mul measurable_snd)
    (fun n => measurePreserving_mul_left μ (n : G)) hρ hρ' hρ1 hρ'1 hρt hρ't hfinv hfi

/-- Exact source type: the observable is only AEMeasurable and weights may be infinite. -/
theorem subgroup_lintegral
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (H : Subgroup G) (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] (μH : Measure H) [SFinite μH]
    (hinv : ∀ f : H → ℝ≥0∞, ∫⁻ n, f n⁻¹ ∂μH = ∫⁻ n, f n ∂μH)
    {ρ ρ' : G → ℝ≥0∞} (hρ : Measurable ρ) (hρ' : Measurable ρ')
    (hρ1 : ∀ g, ∫⁻ n : H, ρ ((n : G) * g) ∂μH = 1) (hρ'1 : ∀ g, ∫⁻ n : H, ρ' ((n : G) * g) ∂μH = 1)
    {φ : G → ℝ≥0∞} (hφ : AEMeasurable φ μ) (hφinv : ∀ (n : H) (g : G), φ ((n : G) * g) = φ g) :
    ∫⁻ g, φ g * ρ g ∂μ = ∫⁻ g, φ g * ρ' g ∂μ := by
  let : MeasurableInv H := ⟨measurable_subtype_coe.inv.subtype_mk⟩
  let := invInvariant_of_lintegral μH hinv
  exact lintegral_mul_eq_of_ae_normalized_smul μH μ
    ((measurable_subtype_coe.comp measurable_fst).mul measurable_snd)
    (fun n => measurePreserving_mul_left μ (n : G)) hφ hφinv hρ hρ'
    (ae_of_all _ fun g _ => hρ1 g) (ae_of_all _ fun g _ => hρ'1 g)

/-- Exact source type, including noncommutative X, right translation and a.e. normalization. -/
theorem right_lintegral
    {G X : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    [AddGroup X] [MeasurableSpace X] [MeasurableNeg X]
    (τ : Measure G) [SFinite τ] [τ.IsMulRightInvariant]
    (μ : Measure X) [SFinite μ] [μ.IsNegInvariant]
    (n : X → G) (hn : Measurable n) (hn_add : ∀ x y, n (x + y) = n x * n y)
    (Φ : G → ℝ≥0∞) (hΦ : Measurable Φ) (hΦn : ∀ g x, Φ (g * n x) = Φ g)
    (w w₀ : G → ℝ≥0∞) (hw : Measurable w) (hw₀ : Measurable w₀)
    (h1 : ∀ᵐ g ∂τ, ∫⁻ x, w (g * n x) ∂μ = 1) (h1₀ : ∀ᵐ g ∂τ, ∫⁻ x, w₀ (g * n x) ∂μ = 1) :
    ∫⁻ g, w g * Φ g ∂τ = ∫⁻ g, w₀ g * Φ g ∂τ := by
  let N : Multiplicative X →* G := MonoidHom.mk' (fun a => n a.toAdd) hn_add
  let : MulAction (Multiplicative X) G := {
    smul := fun a g => g * n (-a.toAdd)
    one_smul := fun g => by
      change g * N (1⁻¹) = g
      simp
    mul_smul := fun a b g => by
      change g * N ((a * b)⁻¹) = (g * N (b⁻¹)) * N (a⁻¹)
      rw [mul_inv_rev, map_mul, mul_assoc] }
  let : MeasurableSpace (Multiplicative X) := ‹MeasurableSpace X›
  let : MeasurableInv (Multiplicative X) :=
    ⟨(show Measurable (fun x : X => -x) from measurable_neg)⟩
  let ν : Measure (Multiplicative X) := μ
  let : SFinite ν := ‹SFinite μ›
  let : ν.IsInvInvariant := ⟨Measure.neg_eq_self μ⟩
  have hact : Measurable fun p : Multiplicative X × G => p.1 • p.2 :=
    measurable_snd.mul (hn.comp (measurable_fst.neg))
  have hpres (a : Multiplicative X) : MeasurePreserving (fun g : G => a • g) τ τ :=
    measurePreserving_mul_right τ (n (-a.toAdd))
  have havg (v : G → ℝ≥0∞) (g : G) :
      ∫⁻ a : Multiplicative X, v (a • g) ∂ν = ∫⁻ x, v (g * n x) ∂μ :=
    lintegral_neg_eq_self (μ := μ) (fun x => v (g * n x))
  have h := lintegral_mul_eq_of_ae_normalized_smul ν τ hact hpres hΦ.aemeasurable
    (fun a g => hΦn g (-a.toAdd)) hw hw₀
    (h1.mono fun g hg _ => (havg w g).trans hg)
    (h1₀.mono fun g hg _ => (havg w₀ g).trans hg)
  simpa only [mul_comm] using h

end CutoffTransportTest
