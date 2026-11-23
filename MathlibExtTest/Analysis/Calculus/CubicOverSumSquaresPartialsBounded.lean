/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Real.Sqrt
import MathlibExt.Analysis.Calculus.CubicOverSumSquaresPartialsBounded

/-!
# Tests for the partial derivatives of `x³ / (x² + y²)`

The function of the exercise is `cubeDivSqAddSq (x, y) = x³ / (x² + y²)`: Lean's convention
`0 / 0 = 0` makes it vanish at the origin, so it satisfies both hypotheses of the module's results.
-/

open MathlibExt.Analysis.Calculus.CubicOverSumSquaresPartialsBounded
  MathlibExt.Analysis.Calculus.CubicOverSumSquaresPartialsBoundedWanted

/-- `x³ / (x² + y²)`, which is `0` at the origin. -/
noncomputable def cubeDivSqAddSq (p : ℝ × ℝ) : ℝ := p.1 ^ 3 / (p.1 ^ 2 + p.2 ^ 2)

theorem cubeDivSqAddSq_zero : cubeDivSqAddSq (0, 0) = 0 := by
  simp [cubeDivSqAddSq]

theorem cubeDivSqAddSq_of_ne :
    ∀ p : ℝ × ℝ, p ≠ (0, 0) → cubeDivSqAddSq p = p.1 ^ 3 / (p.1 ^ 2 + p.2 ^ 2) :=
  fun _ _ => rfl

-- `D₁ f (0, 0) = 1` and `D₂ f (0, 0) = 0`: the slices through the origin are `t` and `0`.
example : deriv (fun t => cubeDivSqAddSq (t, 0)) 0 = 1 :=
  (hasDerivAt_fst_zero cubeDivSqAddSq_zero cubeDivSqAddSq_of_ne).deriv

example : deriv (fun t => cubeDivSqAddSq (0, t)) 0 = 0 := by
  rw [(hasDerivAt_snd cubeDivSqAddSq_zero cubeDivSqAddSq_of_ne 0 0).deriv]
  simp

-- The formulas at `(1, 1)`: `D₁ f = 4 / 4` and `D₂ f = -2 / 4`.
example : deriv (fun t => cubeDivSqAddSq (t, 1)) 1 = 1 := by
  rw [(hasDerivAt_fst cubeDivSqAddSq_zero cubeDivSqAddSq_of_ne (by simp)).deriv]
  norm_num

example : deriv (fun t => cubeDivSqAddSq (1, t)) 1 = -1 / 2 := by
  rw [(hasDerivAt_snd cubeDivSqAddSq_zero cubeDivSqAddSq_of_ne 1 1).deriv]
  norm_num

-- `D₁ f` vanishes on the vertical axis away from the origin: its lower bound `0` is attained.
example (y : ℝ) (hy : y ≠ 0) : deriv (fun t => cubeDivSqAddSq (t, y)) 0 = 0 := by
  rw [(hasDerivAt_fst cubeDivSqAddSq_zero cubeDivSqAddSq_of_ne (by simp [hy])).deriv]
  simp

-- The upper bound `9 / 8` on `D₁ f` is attained at `(√3, 1)`, where `x² = 3 y²`.
example : deriv (fun t => cubeDivSqAddSq (t, 1)) (Real.sqrt 3) = 9 / 8 := by
  rw [(hasDerivAt_fst cubeDivSqAddSq_zero cubeDivSqAddSq_of_ne (by simp)).deriv]
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h4 : Real.sqrt 3 ^ 4 = 9 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h3]
    norm_num
  rw [h3, h4]
  norm_num

-- Unlike the benchmark statement, the strengthened one shows that every slice is differentiable.
example (x y : ℝ) : DifferentiableAt ℝ (fun t => cubeDivSqAddSq (t, y)) x ∧
    DifferentiableAt ℝ (fun t => cubeDivSqAddSq (x, t)) y := by
  obtain ⟨⟨d₁, h₁, -⟩, d₂, h₂, -⟩ :=
    exists_hasDerivAt_partials_bounded cubeDivSqAddSq_zero cubeDivSqAddSq_of_ne x y
  exact ⟨h₁.differentiableAt, h₂.differentiableAt⟩

-- The former `WantedExt` statement, for this function.
example : (∃ M : ℝ, ∀ x y : ℝ, ‖deriv (fun t => cubeDivSqAddSq (t, y)) x‖ ≤ M) ∧
    (∃ M : ℝ, ∀ x y : ℝ, ‖deriv (fun t => cubeDivSqAddSq (x, t)) y‖ ≤ M) :=
  bounded_partialDerivs_cube_div_sq_add_sq cubeDivSqAddSq cubeDivSqAddSq_zero cubeDivSqAddSq_of_ne

#print axioms exists_hasDerivAt_partials_bounded
#print axioms bounded_partialDerivs_cube_div_sq_add_sq
