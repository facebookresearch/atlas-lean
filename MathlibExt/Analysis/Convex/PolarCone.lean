/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Geometry.Convex.Cone.Dual

/-!
# Nonpositive polar membership and the inner dual cone

Let E be a real inner-product space and K any subset of E. The inner dual
cone uses ⟪x,z⟫ ≥ 0 for all x ∈ K. Thus -y belongs to that dual cone exactly
when ⟪x,y⟫ ≤ 0 for all x ∈ K, the nonpositive polar convention.
-/

@[expose] public section

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Nonpositive polar membership through the inner dual cone.** Let E be a real
inner-product space, K ⊆ E an arbitrary set and y : E. Then -y ∈ PointedCone.dual (innerₗ
E) K if and only if ⟪x,y⟫_ℝ ≤ 0 for every x ∈ K. -/
theorem PointedCone.neg_mem_dual_inner_iff {K : Set E} {y : E} :
    -y ∈ PointedCone.dual (innerₗ E) K ↔ ∀ x ∈ K, ⟪x, y⟫_ℝ ≤ 0 := by
  rw [PointedCone.mem_dual]
  simp only [innerₗ_apply_apply, inner_neg_right, neg_nonneg]
