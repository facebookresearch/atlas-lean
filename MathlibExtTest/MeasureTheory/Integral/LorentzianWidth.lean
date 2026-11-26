/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.Integral.LorentzianWidth

/-!
# Tests for width monotonicity of Lorentzian integrals

* The zero measure gives equal integrals and no strict increase.
* `c • δ₀` gives the constant `c` at every positive width.
* `δ₁` gives a strict increase for every `0 < Γ₁ < Γ₂`.
* `c • δ₀ + d • δ₁` increases strictly when `d > 0` and is constant when `d = 0`.
* Equal positive widths are allowed in `integral_lorentzian_mono`.
* Outside the theorems' scope: at width `0` the Dirac mass at the origin increases strictly
  although it has no mass off the origin, and without `0 < Γ₁` a larger second width can
  give a smaller integral.
-/

@[expose] public section

open MeasureTheory

namespace MathlibExtTest.MeasureTheory.Integral.LorentzianWidth

open MathlibExt.MeasureTheory.Integral.LorentzianWidth

/-- The zero measure gives equal integrals at any two widths. -/
example (Γ₁ Γ₂ : ℝ) :
    (∫ E, Γ₁ ^ 2 / (E ^ 2 + Γ₁ ^ 2) ∂(0 : Measure ℝ)) =
      ∫ E, Γ₂ ^ 2 / (E ^ 2 + Γ₂ ^ 2) ∂(0 : Measure ℝ) := by
  simp

/-- The zero measure gives no strict increase. -/
example {Γ₁ Γ₂ : ℝ} (h₁ : 0 < Γ₁) (h : Γ₁ < Γ₂) :
    ¬ ((∫ E, Γ₁ ^ 2 / (E ^ 2 + Γ₁ ^ 2) ∂(0 : Measure ℝ)) <
      ∫ E, Γ₂ ^ 2 / (E ^ 2 + Γ₂ ^ 2) ∂(0 : Measure ℝ)) := by
  rw [integral_lorentzian_lt_iff _ h₁ h]
  simp

/-- `c • δ₀` gives the constant `c` at every positive width. -/
example (c : NNReal) {Γ : ℝ} (hΓ : 0 < Γ) :
    ∫ E, Γ ^ 2 / (E ^ 2 + Γ ^ 2) ∂(c • Measure.dirac (0 : ℝ)) = c := by
  simp [hΓ.ne', NNReal.smul_def]

/-- `δ₁` gives a strict increase for every `0 < Γ₁ < Γ₂`. -/
example {Γ₁ Γ₂ : ℝ} (h₁ : 0 < Γ₁) (h : Γ₁ < Γ₂) :
    (∫ E, Γ₁ ^ 2 / (E ^ 2 + Γ₁ ^ 2) ∂(Measure.dirac (1 : ℝ))) <
      ∫ E, Γ₂ ^ 2 / (E ^ 2 + Γ₂ ^ 2) ∂(Measure.dirac (1 : ℝ)) :=
  (integral_lorentzian_lt_iff _ h₁ h).mpr (by simp)

/-- The mixed measure `c • δ₀ + d • δ₁` puts mass `d` off the origin. -/
private lemma mixed_compl_zero (c d : NNReal) :
    (c • Measure.dirac (0 : ℝ) + d • Measure.dirac (1 : ℝ)) {(0 : ℝ)}ᶜ = d := by
  simp

/-- `c • δ₀ + d • δ₁` increases strictly between two positive widths when `d > 0`. -/
example (c d : NNReal) (hd : 0 < d) {Γ₁ Γ₂ : ℝ} (h₁ : 0 < Γ₁) (h : Γ₁ < Γ₂) :
    (∫ E, Γ₁ ^ 2 / (E ^ 2 + Γ₁ ^ 2)
        ∂(c • Measure.dirac (0 : ℝ) + d • Measure.dirac (1 : ℝ))) <
      ∫ E, Γ₂ ^ 2 / (E ^ 2 + Γ₂ ^ 2)
        ∂(c • Measure.dirac (0 : ℝ) + d • Measure.dirac (1 : ℝ)) :=
  (integral_lorentzian_lt_iff _ h₁ h).mpr (by rw [mixed_compl_zero]; exact_mod_cast hd)

/-- With `d = 0` the mixed measure gives equal integrals at two positive widths. -/
example (c : NNReal) {Γ₁ Γ₂ : ℝ} (h₁ : 0 < Γ₁) (h : Γ₁ < Γ₂) :
    (∫ E, Γ₁ ^ 2 / (E ^ 2 + Γ₁ ^ 2)
        ∂(c • Measure.dirac (0 : ℝ) + (0 : NNReal) • Measure.dirac (1 : ℝ))) =
      ∫ E, Γ₂ ^ 2 / (E ^ 2 + Γ₂ ^ 2)
        ∂(c • Measure.dirac (0 : ℝ) + (0 : NNReal) • Measure.dirac (1 : ℝ)) := by
  refine le_antisymm (integral_lorentzian_mono _ h₁ h.le) (not_lt.mp ?_)
  rw [integral_lorentzian_lt_iff _ h₁ h, mixed_compl_zero]
  simp

/-- Equal positive widths are allowed in `integral_lorentzian_mono`. -/
example (μ : Measure ℝ) [IsFiniteMeasure μ] {Γ : ℝ} (hΓ : 0 < Γ) :
    (∫ E, Γ ^ 2 / (E ^ 2 + Γ ^ 2) ∂μ) ≤ ∫ E, Γ ^ 2 / (E ^ 2 + Γ ^ 2) ∂μ :=
  integral_lorentzian_mono μ hΓ le_rfl

/-- Outside the scope (width `0`): `δ₀` has no mass off the origin, yet the integral increases
strictly from width `0` to width `1`, so `0 < Γ₁` cannot be dropped from the strict criterion. -/
example :
    (∫ E, (0 : ℝ) ^ 2 / (E ^ 2 + (0 : ℝ) ^ 2) ∂(Measure.dirac (0 : ℝ))) <
        ∫ E, (1 : ℝ) ^ 2 / (E ^ 2 + (1 : ℝ) ^ 2) ∂(Measure.dirac (0 : ℝ)) ∧
      ¬ 0 < Measure.dirac (0 : ℝ) {(0 : ℝ)}ᶜ := by
  simp

/-- Outside the scope (nonpositive first width): `-2 ≤ 1`, but against `δ₁` the integral at
width `-2` is larger than at width `1`, so `0 < Γ₁` cannot be dropped from monotonicity. -/
example :
    ¬ ((∫ E, (-2 : ℝ) ^ 2 / (E ^ 2 + (-2 : ℝ) ^ 2) ∂(Measure.dirac (1 : ℝ))) ≤
      ∫ E, (1 : ℝ) ^ 2 / (E ^ 2 + (1 : ℝ) ^ 2) ∂(Measure.dirac (1 : ℝ))) := by
  simp
  norm_num

#print axioms integral_lorentzian_mono
#print axioms integral_lorentzian_lt_iff

end MathlibExtTest.MeasureTheory.Integral.LorentzianWidth
