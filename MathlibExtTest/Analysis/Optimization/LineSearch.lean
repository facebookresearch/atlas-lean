/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Optimization.LineSearch
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecificLimits.Basic

open MathlibExt.Analysis.Optimization.LineSearch

private theorem gradient_half_sq (y : ℝ) : gradient (fun x : ℝ => x ^ 2 / 2) y = y := by
  rw [gradient_eq_deriv']
  have : HasDerivAt (fun x : ℝ => x ^ 2 / 2) (2 * y ^ 1 * 1 / 2) y :=
    ((hasDerivAt_id y).pow 2).div_const 2
  rw [this.deriv]; ring

-- Strong Wolfe steps are standard Wolfe steps.
example {f : ℝ → ℝ} {δ σ x d α : ℝ} (h : StrongWolfeConditions f δ σ x d α) :
    WolfeConditions f δ σ x d α :=
  h.toWolfeConditions

-- Non-vacuity of the Zoutendijk condition: steepest descent with step `1/2` on `x² / 2` from
-- `x 0 = 1` satisfies every hypothesis with `δ = 1/4`, `σ = 1/2` and `L = 1`.
example : Summable fun k : ℕ =>
    inner ℝ (gradient (fun x : ℝ => x ^ 2 / 2) ((1 / 2 : ℝ) ^ k)) (-(1 / 2 : ℝ) ^ k) ^ 2 /
      ‖-(1 / 2 : ℝ) ^ k‖ ^ 2 := by
  have hx : ∀ k : ℕ, (1 / 2 : ℝ) ^ (k + 1) = (1 / 2) ^ k + (1 / 2 : ℝ) • (-(1 / 2 : ℝ) ^ k) := by
    intro k; rw [pow_succ, smul_eq_mul]; ring
  refine zoutendijk (f := fun x : ℝ => x ^ 2 / 2) (δ := 1 / 4) (σ := 1 / 2) (L := 1)
    (by norm_num) (by norm_num) (by norm_num) hx (fun _ => by norm_num) ?_ ?_ ?_ ?_
  · intro k
    rw [gradient_half_sq]
    simp only [RCLike.inner_apply, conj_trivial]
    have : 0 < (1 / 2 : ℝ) ^ k := by positivity
    nlinarith
  · intro k
    have : 0 < (1 / 2 : ℝ) ^ k := by positivity
    refine ⟨?_, ?_⟩
    · unfold ArmijoCondition
      rw [gradient_half_sq]
      simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul]
      nlinarith
    · unfold CurvatureCondition
      rw [gradient_half_sq, gradient_half_sq]
      simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul]
      nlinarith
  · intro k
    rw [gradient_half_sq, gradient_half_sq, one_mul]
  · exact ⟨0, by rintro _ ⟨k, rfl⟩; positivity⟩
