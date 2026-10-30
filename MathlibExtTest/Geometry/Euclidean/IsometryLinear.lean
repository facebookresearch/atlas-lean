/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Euclidean.IsometryLinear

@[expose] public section

/-- The identity isometry of Euclidean space fixes `0` and is linear. -/
example : IsLinearMap ℝ
    (id : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) :=
  isometry_isLinearMap_of_map_zero id isometry_id (by rfl)

/-- Negation is an isometry of Euclidean space fixing `0`, hence linear. -/
example : IsLinearMap ℝ
    (fun x : EuclideanSpace ℝ (Fin 2) => -x) := by
  apply isometry_isLinearMap_of_map_zero (fun x : EuclideanSpace ℝ (Fin 2) => -x)
  · intro x y
    simp
  · simp

/-- The affine decomposition of the identity isometry is `x = x + 0`. -/
example (x : EuclideanSpace ℝ (Fin 2)) :
    (id : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) x =
      (isometry_id (α := EuclideanSpace ℝ (Fin 2))).affineIsometryOfStrictConvexSpace.toAffineMap.linear x +
        (id : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) 0 :=
  isometry_apply_eq_linear_apply_add_map_zero
    (id : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) isometry_id x

/-- Linearity from the main theorem unfolds to additivity and homogeneity. -/
example (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hf : Isometry f) (hf0 : f 0 = 0) (x y : EuclideanSpace ℝ (Fin 2))
    (c : ℝ) :
    f (x + y) = f x + f y ∧ f (c • x) = c • f x :=
  ⟨(isometry_isLinearMap_of_map_zero f hf hf0).map_add x y,
    (isometry_isLinearMap_of_map_zero f hf hf0).map_smul c x⟩
