/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Euclidean.HypersurfaceCurvature

/-!
# Tests for the curvature of level-set hypersurfaces of Euclidean space
-/

open EuclideanGeometry Module
open scoped ContDiff

noncomputable section

/-- The unit sphere of `ℝ³` has mean curvature `2` for the outward normal. -/
example (p : EuclideanSpace ℝ (Fin 3)) (hp : ‖p‖ = 1) :
    levelSetMeanCurvature (fun x : EuclideanSpace ℝ (Fin 3) ↦ ‖x‖ ^ 2 - 1) p = 2 := by
  rw [levelSetMeanCurvature_sphere p hp, finrank_euclideanSpace, Fintype.card_fin]
  norm_num

/-- With the inward normal the sign flips. -/
example (p : EuclideanSpace ℝ (Fin 3)) (hp : ‖p‖ = 1) :
    levelSetMeanCurvature (-fun x : EuclideanSpace ℝ (Fin 3) ↦ ‖x‖ ^ 2 - 1) p = -2 := by
  rw [levelSetMeanCurvature_neg, levelSetMeanCurvature_sphere p hp, finrank_euclideanSpace,
    Fintype.card_fin]
  norm_num

/-- A positive rescaling of the defining function does not change the mean curvature. -/
example (p : EuclideanSpace ℝ (Fin 3)) (hp : ‖p‖ = 1) :
    levelSetMeanCurvature ((5 : ℝ) • fun x : EuclideanSpace ℝ (Fin 3) ↦ ‖x‖ ^ 2 - 1) p = 2 := by
  rw [levelSetMeanCurvature_smul_of_pos _ _ (by norm_num), levelSetMeanCurvature_sphere p hp,
    finrank_euclideanSpace, Fintype.card_fin]
  norm_num

/-- Planes are minimal. -/
example (a p : EuclideanSpace ℝ (Fin 3)) :
    levelSetMeanCurvature (fun x : EuclideanSpace ℝ (Fin 3) ↦ inner ℝ a x - 1) p = 0 :=
  levelSetMeanCurvature_affine a 1 p

/-- `‖x‖² - 1` is a local defining function of the unit sphere at each of its points. -/
example (p : EuclideanSpace ℝ (Fin 3)) (hp : ‖p‖ = 1) :
    IsLocalDefiningFunction (Metric.sphere 0 1)
      (fun x : EuclideanSpace ℝ (Fin 3) ↦ ‖x‖ ^ 2 - 1) p := by
  refine ⟨by simp [hp], (contDiff_norm_sq ℝ).contDiffAt.sub contDiffAt_const, ?_, ?_⟩
  · rw [fderiv_sub_const, fderiv_norm_sq_apply]
    intro h
    have h1 := congrArg (fun L ↦ L p) h
    simp only [smul_apply, innerSL_apply_apply, real_inner_self_eq_norm_sq, hp, zero_apply] at h1
    norm_num at h1
  · refine Filter.Eventually.of_forall fun x ↦ ?_
    simp only [mem_sphere_iff_norm, sub_zero, sub_eq_zero]
    constructor
    · intro h; rw [h]; norm_num
    · intro h
      have h0 : 0 ≤ ‖x‖ := norm_nonneg x
      nlinarith [sq_nonneg (‖x‖ - 1), sq_nonneg (‖x‖ + 1)]

/-- A point off the zero set has no local defining function, even when the zero set of `ρ` misses
a neighborhood of the point. -/
example : ¬ IsLocalDefiningFunction (∅ : Set ℝ) (fun x : ℝ ↦ x + 1) 0 := by
  intro h
  exact absurd h.mem (Set.notMem_empty 0)

/-- Statement shape: a domain `Ω = {ρ < 0}` of `ℝⁿ` with smooth mean-convex boundary (add
`Bornology.IsBounded Ω` for a bounded domain). -/
example (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ ρ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ ρ ∧ Ω = {x | ρ x < 0} ∧
    (∀ x, ρ x = 0 → fderiv ℝ ρ x ≠ 0) ∧ ∀ x, ρ x = 0 → 0 ≤ levelSetMeanCurvature ρ x
