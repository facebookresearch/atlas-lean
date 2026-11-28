/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Moments.Variance

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Identifying a linear degradation path from two noisy readings -/

@[expose] public section

open MeasureTheory

namespace MathlibExt.Probability.Statistics

/-- The observation law at times `t₁` and `t₂` for intercept and slope `θ = (θ₀, θ₁)`.
The coordinates of `e` have the fixed joint noise law `P`, which need not be a product. -/
noncomputable def linearDegradationLaw (P : Measure (ℝ × ℝ)) (t₁ t₂ : ℝ) (θ : ℝ × ℝ) :
    Measure (ℝ × ℝ) :=
  P.map fun e => (θ.1 + θ.2 * t₁ + e.1, θ.1 + θ.2 * t₂ + e.2)

/-- With centered integrable noise, the two observed means are the two values of the path. -/
private theorem linearDegradationLaw_means (P : Measure (ℝ × ℝ)) [IsProbabilityMeasure P]
    (h₁ : Integrable (Prod.fst : ℝ × ℝ → ℝ) P) (h₂ : Integrable (Prod.snd : ℝ × ℝ → ℝ) P)
    (hmean₁ : (∫ e : ℝ × ℝ, e.1 ∂P) = 0) (hmean₂ : (∫ e : ℝ × ℝ, e.2 ∂P) = 0)
    (t₁ t₂ : ℝ) (θ : ℝ × ℝ) :
    let Q := linearDegradationLaw P t₁ t₂ θ
    (∫ y : ℝ × ℝ, y.1 ∂Q) = θ.1 + θ.2 * t₁ ∧
      (∫ y : ℝ × ℝ, y.2 ∂Q) = θ.1 + θ.2 * t₂ := by
  dsimp only [linearDegradationLaw]
  constructor
  · rw [integral_map (by fun_prop) measurable_fst.aestronglyMeasurable,
      integral_add (integrable_const _) h₁, integral_const, probReal_univ, one_smul,
      hmean₁, add_zero]
  · rw [integral_map (by fun_prop) measurable_snd.aestronglyMeasurable,
      integral_add (integrable_const _) h₂, integral_const, probReal_univ, one_smul,
      hmean₂, add_zero]

/-- **Identifiability of a linear degradation path.** For a fixed centered joint noise law
with square-integrable coordinates, the law of the two readings identifies both the
intercept and the slope exactly when the two design times differ. For distinct times, if
`m₁` and `m₂` are the observed means, the slope is `(m₂ - m₁) / (t₂ - t₁)` and the
intercept is `m₁ - t₁ * ((m₂ - m₁) / (t₂ - t₁))`. At a repeated time `t` the distinct
parameters `(0, 0)` and `(-t, 1)` give the same joint law. -/
theorem linearDegradation_identifiability (P : Measure (ℝ × ℝ)) [IsProbabilityMeasure P]
    (h₁ : MemLp (Prod.fst : ℝ × ℝ → ℝ) 2 P) (h₂ : MemLp (Prod.snd : ℝ × ℝ → ℝ) 2 P)
    (hmean₁ : (∫ e : ℝ × ℝ, e.1 ∂P) = 0) (hmean₂ : (∫ e : ℝ × ℝ, e.2 ∂P) = 0)
    (t₁ t₂ : ℝ) :
    (Function.Injective (linearDegradationLaw P t₁ t₂) ↔ t₁ ≠ t₂) ∧
      (t₁ ≠ t₂ → ∀ θ : ℝ × ℝ,
        let Q := linearDegradationLaw P t₁ t₂ θ
        let m₁ := ∫ y : ℝ × ℝ, y.1 ∂Q
        let m₂ := ∫ y : ℝ × ℝ, y.2 ∂Q
        θ.2 = (m₂ - m₁) / (t₂ - t₁) ∧ θ.1 = m₁ - t₁ * ((m₂ - m₁) / (t₂ - t₁))) ∧
      linearDegradationLaw P t₁ t₁ (0, 0) = linearDegradationLaw P t₁ t₁ (-t₁, 1) := by
  have hsame : linearDegradationLaw P t₁ t₁ (0, 0) =
      linearDegradationLaw P t₁ t₁ (-t₁, 1) := by
    simp [linearDegradationLaw]
  have hrecover (ht : t₁ ≠ t₂) (θ : ℝ × ℝ) :
      let Q := linearDegradationLaw P t₁ t₂ θ
      let m₁ := ∫ y : ℝ × ℝ, y.1 ∂Q
      let m₂ := ∫ y : ℝ × ℝ, y.2 ∂Q
      θ.2 = (m₂ - m₁) / (t₂ - t₁) ∧ θ.1 = m₁ - t₁ * ((m₂ - m₁) / (t₂ - t₁)) := by
    obtain ⟨hm₁, hm₂⟩ := linearDegradationLaw_means P (h₁.integrable one_le_two)
      (h₂.integrable one_le_two) hmean₁ hmean₂ t₁ t₂ θ
    dsimp only at hm₁ hm₂ ⊢
    rw [hm₁, hm₂]
    have hslope : θ.2 = ((θ.1 + θ.2 * t₂) - (θ.1 + θ.2 * t₁)) / (t₂ - t₁) := by
      apply (eq_div_iff (sub_ne_zero.mpr ht.symm)).2
      ring
    refine ⟨hslope, ?_⟩
    rw [← hslope]
    ring
  refine ⟨⟨?_, ?_⟩, hrecover, hsame⟩
  · intro hinj ht
    subst t₂
    have hp := hinj hsame
    have hzero : (0 : ℝ) = 1 := congrArg Prod.snd hp
    exact zero_ne_one hzero
  · intro ht θ η heq
    obtain ⟨hslopeθ, hinterceptθ⟩ := hrecover ht θ
    obtain ⟨hslopeη, hinterceptη⟩ := hrecover ht η
    rw [heq] at hslopeθ hinterceptθ
    exact Prod.ext (hinterceptθ.trans hinterceptη.symm) (hslopeθ.trans hslopeη.symm)

/-- An unknown common additive measurement bias is confounded with the intercept: shifting
both coordinates of the fixed noise by `c` and decreasing the intercept by `c` leaves the
observation law unchanged, including when the two observation times differ. -/
theorem linearDegradationLaw_shift_noise (P : Measure (ℝ × ℝ)) (t₁ t₂ : ℝ)
    (θ : ℝ × ℝ) (c : ℝ) :
    linearDegradationLaw (P.map fun e : ℝ × ℝ => (e.1 + c, e.2 + c)) t₁ t₂ (θ.1 - c, θ.2) =
      linearDegradationLaw P t₁ t₂ θ := by
  simp only [linearDegradationLaw]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext e
  apply Prod.ext <;> dsimp [Function.comp_def] <;> ring

end MathlibExt.Probability.Statistics
