/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Robust linear constraints under ellipsoidal uncertainty

In robust linear programming (Ben-Tal and Nemirovski) the data of a linear constraint are only
known to lie in an uncertainty set, and a solution must satisfy the constraint for every
realization. When the data run through an ellipsoid, the image of the unit ball under an affine
map, the robust counterpart of the linear constraint is a single conic quadratic constraint.
Following A. Ben-Tal and A. Nemirovski, *Lectures on Modern Convex Optimization* (2020–2023
lecture notes), Section 2.4.1, derivation of (RLP); the perturbation space `U` and the space of
decisions `E` are real Hilbert spaces, and `†` is the adjoint:

* `forall_norm_le_one_le_add_inner_iff`: `c + ⟪u, v⟫ ≥ 0` for all `‖u‖ ≤ 1` iff `‖v‖ ≤ c`.
* `robust_linear_constraint_iff`: `⟪a, x⟫ - b ≥ 0` for all `(a, b) = (a⋆ + A u, b⋆ + ⟪q, u⟫)`
  with `‖u‖ ≤ 1` iff `‖A† x - q‖ ≤ ⟪a⋆, x⟫ - b⋆`.
* `robust_objective_le_iff`: `⟪c, x⟫ ≤ t` for all `c = c⋆ + P u` with `‖u‖ ≤ 1` iff
  `⟪c⋆, x⟫ + ‖P† x‖ ≤ t`.
-/

@[expose] public section

open scoped RealInnerProductSpace

namespace MathlibExt.Analysis.Convex.RobustLinearProgramming

variable {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

/-- **Minimum of a linear form over the unit ball.** For `c : ℝ` and `v` in a real inner product
space, `c + ⟪u, v⟫ ≥ 0` for every `u` with `‖u‖ ≤ 1` if and only if `‖v‖ ≤ c`, since the minimum
of `⟪u, v⟫` over the unit ball is `-‖v‖`. This is the computation
`min_{uᵀu ≤ 1} uᵀ Pᵀ (x; -1) = -‖Pᵀ (x; -1)‖₂` in A. Ben-Tal and A. Nemirovski, *Lectures on
Modern Convex Optimization*, Section 2.4.1. -/
theorem forall_norm_le_one_le_add_inner_iff {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (c : ℝ) (v : F) :
    (∀ u : F, ‖u‖ ≤ 1 → 0 ≤ c + ⟪u, v⟫) ↔ ‖v‖ ≤ c := by
  constructor
  · intro h
    have hu : ‖-(‖v‖⁻¹ • v)‖ ≤ 1 := by
      rw [norm_neg, norm_smul, norm_inv, norm_norm]
      rcases eq_or_ne ‖v‖ 0 with h0 | h0
      · simp [h0]
      · rw [inv_mul_cancel₀ h0]
    have := h _ hu
    rw [inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at this
    rcases eq_or_ne ‖v‖ 0 with h0 | h0
    · simp [h0] at this ⊢; linarith
    · have : ‖v‖⁻¹ * ‖v‖ ^ 2 = ‖v‖ := by field_simp
      linarith
  · intro h u hu
    have h1 : -(‖u‖ * ‖v‖) ≤ ⟪u, v⟫ := by
      have := abs_real_inner_le_norm u v
      linarith [neg_abs_le ⟪u, v⟫]
    have h2 : ‖u‖ * ‖v‖ ≤ ‖v‖ := by
      have := norm_nonneg v
      nlinarith [norm_nonneg u]
    linarith

/-- **Robust counterpart of a linear constraint under ellipsoidal uncertainty.** Let the data
`(a, b)` of the constraint `⟪a, x⟫ - b ≥ 0` run through the ellipsoid
`{(a⋆ + A u, b⋆ + ⟪q, u⟫) : ‖u‖ ≤ 1}`, with `A : U →L[ℝ] E` and `q ∈ U`. Then `x` satisfies the
constraint for every realization of the data if and only if it satisfies the conic quadratic
constraint `‖A† x - q‖ ≤ ⟪a⋆, x⟫ - b⋆`. This is the derivation of the constraints of (RLP) in
A. Ben-Tal and A. Nemirovski, *Lectures on Modern Convex Optimization* (lecture notes,
2020–2023), Section 2.4.1, where the perturbation `P u` of `(a; b)` has block rows `A` and `qᵀ`,
so that `Pᵀ (x; -1) = A† x - q`. -/
theorem robust_linear_constraint_iff (aStar x : E) (bStar : ℝ) (A : U →L[ℝ] E) (q : U) :
    (∀ u : U, ‖u‖ ≤ 1 → 0 ≤ ⟪aStar + A u, x⟫ - (bStar + ⟪q, u⟫)) ↔
      ‖ContinuousLinearMap.adjoint A x - q‖ ≤ ⟪aStar, x⟫ - bStar := by
  rw [← forall_norm_le_one_le_add_inner_iff]
  refine forall_congr' fun u => imp_congr_right fun _ => ?_
  rw [inner_add_left, inner_sub_right, ContinuousLinearMap.adjoint_inner_right,
    real_inner_comm q u]
  constructor <;> intro h <;> linarith

/-- **Robust counterpart of a linear objective under ellipsoidal uncertainty.** For
`P : U →L[ℝ] E`, the inequality `⟪c, x⟫ ≤ t` holds for every `c = c⋆ + P u` with `‖u‖ ≤ 1` if and
only if `⟪c⋆, x⟫ + ‖P† x‖ ≤ t`. This is the objective part of (RLP) in A. Ben-Tal and
A. Nemirovski, *Lectures on Modern Convex Optimization* (lecture notes, 2020–2023),
Section 2.4.1. -/
theorem robust_objective_le_iff (cStar x : E) (P : U →L[ℝ] E) (t : ℝ) :
    (∀ u : U, ‖u‖ ≤ 1 → ⟪cStar + P u, x⟫ ≤ t) ↔
      ⟪cStar, x⟫ + ‖ContinuousLinearMap.adjoint P x‖ ≤ t := by
  have key := forall_norm_le_one_le_add_inner_iff (t - ⟪cStar, x⟫)
    (-(ContinuousLinearMap.adjoint P x))
  rw [norm_neg] at key
  rw [show (⟪cStar, x⟫ + ‖ContinuousLinearMap.adjoint P x‖ ≤ t) ↔
      (‖ContinuousLinearMap.adjoint P x‖ ≤ t - ⟪cStar, x⟫) by constructor <;> intro h <;> linarith,
    ← key]
  refine forall_congr' fun u => imp_congr_right fun _ => ?_
  rw [inner_add_left, inner_neg_right, ContinuousLinearMap.adjoint_inner_right]
  constructor <;> intro h <;> linarith

end MathlibExt.Analysis.Convex.RobustLinearProgramming
