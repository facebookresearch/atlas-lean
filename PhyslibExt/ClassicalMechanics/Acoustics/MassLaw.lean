/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Limp-panel mass law

## i. Overview

For the dimensionless ratio `x = ω * m / (2 * ρ * c) > 0`
(`ω` angular frequency, `m` the panel surface mass density in
kg/m^2, `ρ` air density, `c` the speed of sound in air) and the
declared normal-incidence limp-panel model `τ = 1 / (1 + x ^ 2)`,
the
transmission loss `10 * log10 (1 / τ) = 10 * log10 (1 + x ^ 2)`
splits into the mass-law asymptote `20 * log10 x` plus the
positive correction `10 * log10 (1 + x ^ (-2))`. The loss strictly
exceeds the asymptote, and doubling `x` adds `20 * log10 2` to the
asymptote.

## ii. Key results

- `Acoustics.mass_law_comparison`: the asymptote split, the strict
  excess, and the doubling law.

## iii. Table of contents

- A. Mass-law comparison

## iv. References

- L. L. Beranek and I. L. Vér (eds.), *Noise and Vibration
  Control Engineering*, Wiley, 1992 (mass law for a limp panel at
  normal incidence).
-/

@[expose] public section

namespace Acoustics

/-! ## A. Mass-law comparison -/

/-- Declared limp-panel mass law. For the dimensionless ratio
`x = ω * m / (2 * ρ * c) > 0` and the supplied normal-incidence
panel model `τ = 1 / (1 + x ^ 2)`, the transmission loss
`10 * log10 (1 / τ) = 10 * log10 (1 + x ^ 2)` splits as the mass-law
asymptote `20 * log10 x` plus the positive correction
`10 * log10 (1 + x ^ (-2 : ℤ))`; hence it strictly exceeds the
asymptote, and doubling `x` adds `20 * log10 2` to the asymptote. -/
theorem mass_law_comparison {x : ℝ} (hx : 0 < x) :
    10 * Real.logb 10 (1 + x ^ 2)
      = 20 * Real.logb 10 x + 10 * Real.logb 10 (1 + x ^ (-2 : ℤ))
    ∧ 20 * Real.logb 10 x < 10 * Real.logb 10 (1 + x ^ 2)
    ∧ 20 * Real.logb 10 (2 * x)
      = 20 * Real.logb 10 x + 20 * Real.logb 10 2 := by
  have hx' : x ≠ 0 := ne_of_gt hx
  have hx2 : (0 : ℝ) < x ^ 2 := by positivity
  have hz : (0 : ℝ) < x ^ (-2 : ℤ) := zpow_pos hx (-2)
  have h1z0 : (0 : ℝ) < 1 + x ^ (-2 : ℤ) := by linarith
  have h1z : (1 : ℝ) < 1 + x ^ (-2 : ℤ) := by linarith
  have hfactor : (1 : ℝ) + x ^ 2 = x ^ 2 * (1 + x ^ (-2 : ℤ)) := by
    field_simp
    ring
  have hmul : Real.logb 10 (x ^ 2 * (1 + x ^ (-2 : ℤ)))
      = Real.logb 10 (x ^ 2) + Real.logb 10 (1 + x ^ (-2 : ℤ)) :=
    Real.logb_mul (ne_of_gt hx2) (ne_of_gt h1z0)
  have hsplit : Real.logb 10 (1 + x ^ 2)
      = 2 * Real.logb 10 x + Real.logb 10 (1 + x ^ (-2 : ℤ)) := by
    rw [hfactor, hmul, Real.logb_pow]
    norm_num
  have hcorr : (0 : ℝ) < Real.logb 10 (1 + x ^ (-2 : ℤ)) :=
    Real.logb_pos (by norm_num) h1z
  have hdouble : Real.logb 10 (2 * x) = Real.logb 10 2 + Real.logb 10 x :=
    Real.logb_mul (by norm_num) hx'
  refine ⟨?_, ?_, ?_⟩
  · rw [hsplit]; ring
  · rw [hsplit]
    have h10 : (0 : ℝ) < 10 * Real.logb 10 (1 + x ^ (-2 : ℤ)) :=
      mul_pos (by norm_num) hcorr
    linarith
  · rw [hdouble]; ring

/-- The mass-law split: transmission loss equals the asymptote
plus the positive correction term. -/
lemma mass_law_split {x : ℝ} (hx : 0 < x) :
    10 * Real.logb 10 (1 + x ^ 2)
      = 20 * Real.logb 10 x + 10 * Real.logb 10 (1 + x ^ (-2 : ℤ)) :=
  (mass_law_comparison hx).1

/-- The transmission loss strictly exceeds the mass-law asymptote. -/
lemma mass_law_gt_asymptote {x : ℝ} (hx : 0 < x) :
    20 * Real.logb 10 x < 10 * Real.logb 10 (1 + x ^ 2) :=
  (mass_law_comparison hx).2.1

/-- Doubling `x` adds `20 * log10 2` to the asymptote. -/
lemma mass_law_asymptote_double {x : ℝ} (hx : 0 < x) :
    20 * Real.logb 10 (2 * x)
      = 20 * Real.logb 10 x + 20 * Real.logb 10 2 :=
  (mass_law_comparison hx).2.2

end Acoustics
