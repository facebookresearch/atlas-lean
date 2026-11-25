/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Variational.MinimizingMovementContraction
public import MathlibExtTest.Analysis.Variational.MinimizingMovement
import Mathlib.Tactic.Linarith

@[expose] public section

open Set MathlibExt.Analysis.Variational.MinimizingMovement
  MathlibExtTest.Analysis.Variational.MinimizingMovement

namespace MathlibExtTest.Analysis.Variational.MinimizingMovementContraction

/-- The quadratic energy `λ z² / 2` on `ℝ` is `λ`-convex (with equality in the defining
inequality). -/
theorem strongConvexOn_quadratic (lam : ℝ) :
    StrongConvexOn (univ : Set ℝ) lam (fun z : ℝ => lam * z ^ 2 / 2) := by
  refine ⟨convex_univ, fun x _ y _ a b _ _ hab => ?_⟩
  simp only [smul_eq_mul, Real.norm_eq_abs, sq_abs]
  have hb : b = 1 - a := by linarith
  subst hb
  ring_nf
  exact le_refl _

/-- Non-vacuity: two discrete trajectories `x / (1 + hλ)ᵏ` of the quadratic energy contract at
the rate `(1 + hλ)⁻ᵏ`. -/
example {lam h : ℝ} (hlam : 0 ≤ lam) (hh : 0 < h) (x₁ x₂ : ℝ) (k : ℕ) :
    (1 + lam * h) ^ k * ‖x₁ / (1 + h * lam) ^ k - x₂ / (1 + h * lam) ^ k‖ ≤
      ‖x₁ / (1 + h * lam) ^ 0 - x₂ / (1 + h * lam) ^ 0‖ :=
  (isMinimizingMovement_quadratic hlam hh x₁).contraction_pow (strongConvexOn_quadratic lam) hh
    (by positivity) (isMinimizingMovement_quadratic hlam hh x₂) k

end MathlibExtTest.Analysis.Variational.MinimizingMovementContraction
