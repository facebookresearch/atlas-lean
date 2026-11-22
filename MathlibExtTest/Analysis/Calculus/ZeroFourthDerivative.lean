/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

import MathlibExt.Analysis.Calculus.ZeroFourthDerivative

/-!
# Zero-fourth-derivative checks

Focused checks for `MathlibExt.Analysis.Calculus.ZeroFourthDerivative`: the constancy lemma on a
constant function and the cubic lemma on `x ^ 3` and on `x ^ 3 - x ^ 2`, whose fourth
derivatives vanish.

These are elaboration and non-vacuity checks, not new results.
-/

open MathlibExt.Analysis.Calculus.ZeroFourthDerivative

/-- Constancy on `[0, 1]` for a constant function. -/
example : (fun _ : ℝ => (5 : ℝ)) 1 = (fun _ : ℝ => (5 : ℝ)) 0 :=
  eq_of_deriv_eq_zero_on_Ioo (L := 1) (f := fun _ : ℝ => (5 : ℝ)) (differentiable_const _)
    (fun x _ => deriv_const x 5) ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩

/-- The cubic `x ^ 3` has zero fourth derivative, so it agrees with a cubic on `[0, 1]`. -/
example : ∃ c₀ c₁ c₂ c₃ : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
    (fun x : ℝ => x ^ 3) x = c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3 :=
  exists_cubic_of_iteratedDeriv_four_eq_zero (by fun_prop)
    (fun x _ => by simp [iteratedDeriv_pow])

/-- The same on `[0, 2]` for `x ^ 3 - x ^ 2`. -/
example : ∃ c₀ c₁ c₂ c₃ : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 2,
    (fun x : ℝ => x ^ 3 - x ^ 2) x = c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3 := by
  refine exists_cubic_of_iteratedDeriv_four_eq_zero (by fun_prop) (fun x _ => ?_)
  rw [iteratedDeriv_fun_sub (by fun_prop) (by fun_prop)]
  simp [iteratedDeriv_pow]
