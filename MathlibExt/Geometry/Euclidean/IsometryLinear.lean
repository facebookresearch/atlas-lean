/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.StrictConvexBetween
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# Isometries of Euclidean space are affine, and linear when they fix `0`

This file ports the general-`n` isometry lemma from the Isometries section of
`v1/Atlas/AlgebraNotes`: every isometry of
`EuclideanSpace ℝ (Fin n)` is an affine map, and an isometry fixing `0` is a
linear map. This is the Mazur–Ulam phenomenon for Euclidean space, specialised
from Mathlib's `Isometry.affineIsometryOfStrictConvexSpace`.

This is distinct from the plane (`n = 2`) classification into translations,
rotations, reflections and glide reflections, which the book treats separately:
the results here hold for every `n` and are not used in that classification.

## Main results

* `isometry_apply_eq_linear_apply_add_map_zero`: every isometry `f` of
  Euclidean space satisfies `f x = A x + f 0`, where `A` is the linear part of
  the affine isometry associated to `f`.
* `isometry_isLinearMap_of_map_zero`: if in addition `f 0 = 0`, then `f` is a
  linear map (`IsLinearMap ℝ f`).
-/

/-- **Isometries of Euclidean space are affine.** For every natural number $n$, every
isometry $f$ of the Euclidean space $\mathbb{R}^n$ is affine: there is a linear map
$A : \mathbb{R}^n \to \mathbb{R}^n$, the linear part of $f$, such that $f(x) = A x + f(0)$
for every $x \in \mathbb{R}^n$. -/
theorem isometry_apply_eq_linear_apply_add_map_zero {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : Isometry f) (x : EuclideanSpace ℝ (Fin n)) :
    f x = hf.affineIsometryOfStrictConvexSpace.toAffineMap.linear x + f 0 := by
  have key := congr_fun hf.affineIsometryOfStrictConvexSpace.toAffineMap.decomp x
  simpa using key

/-- **Isometries of Euclidean space fixing the origin are linear.** For every natural
number $n$, if $f$ is an isometry of the Euclidean space $\mathbb{R}^n$ with $f(0) = 0$, then
$f$ is $\mathbb{R}$-linear: $f(x + y) = f(x) + f(y)$ and $f(c x) = c f(x)$ for all
$x, y \in \mathbb{R}^n$ and $c \in \mathbb{R}$. -/
theorem isometry_isLinearMap_of_map_zero {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : Isometry f) (hf0 : f 0 = 0) :
    IsLinearMap ℝ f := by
  have hlin : ∀ x, f x =
      hf.affineIsometryOfStrictConvexSpace.toAffineMap.linear x := by
    intro x
    rw [isometry_apply_eq_linear_apply_add_map_zero f hf x, hf0, add_zero]
  exact { map_add := by
            intro x y
            rw [hlin x, hlin y, hlin (x + y), map_add]
          map_smul := by
            intro c x
            rw [hlin x, hlin (c • x), map_smul] }
