/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Hypercontractivity.LevelInequalities
import Mathlib.Tactic.NormNum

open BooleanCube
open scoped BigOperators

/-! ### The Level-k Inequalities -/

/-- The Level-2 Inequality for any `{0, 1}`-valued function satisfying the size condition. -/
example (f : BoolCube 6 → ℝ) (hf : ∀ x, f x = 0 ∨ f x = 1)
    (h : (2 : ℝ) ≤ 2 * Real.log (1 / 𝔼 x, f x)) :
    ∑ S with S.card ≤ 2, boolFourierCoeff 6 f S ^ 2 ≤
      (2 * Real.exp 1 / 2 * Real.log (1 / 𝔼 x, f x)) ^ 2 * (𝔼 x, f x) ^ 2 := by
  exact_mod_cast level_k_inequality (k := 2) hf (by norm_num) (by exact_mod_cast h)

/-- The Level-1 Inequality, instantiated for a function on the 5-cube of mean at most `1/2`. -/
example : ∃ C : ℝ, ∀ f : BoolCube 5 → ℝ, (∀ x, f x = 0 ∨ f x = 1) → 𝔼 x, f x ≤ 1 / 2 →
    ∑ S with S.card = 1, boolFourierCoeff 5 f S ^ 2 ≤
      C * (𝔼 x, f x) ^ 2 * Real.log (1 / 𝔼 x, f x) := by
  obtain ⟨C, hC⟩ := level_one_inequality
  exact ⟨C, fun f hf h => hC 5 f hf h⟩

/-- The Level-1 Inequality applied to the indicator of the empty set. -/
example : ∃ C : ℝ, ∑ S with S.card = 1, boolFourierCoeff 3 (fun _ => 0) S ^ 2 ≤
    C * (𝔼 _x : BoolCube 3, (0 : ℝ)) ^ 2 * Real.log (1 / 𝔼 _x : BoolCube 3, (0 : ℝ)) := by
  obtain ⟨C, hC⟩ := level_one_inequality
  exact ⟨C, hC 3 (fun _ => 0) (fun _ => Or.inl rfl) (by simp)⟩
