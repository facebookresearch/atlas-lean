/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.WeilExplicitFormula

/-!
# Tests for Weil's explicit formula

The auxiliary hypothesis `h (it) = h₀ (t / 2π)` determines `h₀` on all of `ℝ` and is always
satisfiable; the formula is instantiated at an actual enumeration of the zeros (with the trivial
test function `h = 0`, for which the remaining hypotheses hold).
-/

@[expose] public section

open Complex RiemannXi

namespace WeilExplicitFormulaTest

/-- For every `h`, the function `h₀ u = h (2π u i)` satisfies `h (t i) = h₀ (t / 2π)`. -/
example (h : ℂ → ℂ) : ∃ h0 : ℝ → ℂ, ∀ t : ℝ, h (t * I) = h0 (t / (2 * Real.pi)) := by
  refine ⟨fun u => h ((2 * Real.pi * u : ℝ) * I), fun t => ?_⟩
  congr 2
  field_simp

/-- The formula, instantiated at an enumeration and `h = 0`. -/
example : ∃ (ι : Type) (z : ι → ℂ) (S P : ℂ),
    HasSum (fun n => if 0 < (z n).im then (0 : ℂ) else 0) S ∧
    HasSum (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      FourierTransform.fourier (fun _ : ℝ => (0 : ℂ)) (Real.log n)) P ∧
    S + P = 0 - 1 / 2 * (Real.log Real.pi : ℂ) *
      FourierTransform.fourier (fun _ : ℝ => (0 : ℂ)) 0 +
        1 / 2 * ∫ t : ℝ, digamma (1 / 4 + I * Real.pi * t) * 0 := by
  obtain ⟨ι, z, hz⟩ := exists_card_eq_analyticOrderAt
  obtain ⟨S, P, hS, hP, hSP⟩ := weil_explicit_formula (ε := 1) one_pos (h := fun _ => 0)
    (differentiableOn_const 0) (fun _ => rfl) ⟨0, fun s _ _ => by simp⟩
    (h0 := fun _ => 0) (fun _ => rfl) z hz
  exact ⟨ι, z, S, P, hS, hP, hSP⟩

end WeilExplicitFormulaTest
