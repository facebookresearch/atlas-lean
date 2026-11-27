/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Coordinate criterion for the complex unit sphere

For any finite index type I, use the canonical Euclidean space ℂ^I and its
Hermitian ℓ² norm. A vector lies on the sphere centered at zero of radius one
exactly when the sum of star(x_i)*x_i is one. The criterion uses Metric.sphere;
there is no separate normalized-vector carrier. Empty index types give an
empty unit sphere, and the coordinates retain their original complex scalar
and conjugation conventions.
-/

@[expose] public section
open scoped BigOperators InnerProductSpace

namespace EuclideanSpace
universe uI

/-- **Coordinate criterion for the complex Euclidean unit sphere.** Let I be any finite
index type and x : EuclideanSpace ℂ I. With the canonical Hermitian ℓ² norm,
x∈Metric.sphere(0)1 if and only if ∑i star(x_i)*x_i=1 in ℂ. The empty-index case is
included: the sum is zero and the unit sphere is empty. -/
theorem mem_sphere_zero_one_iff_sum_star_mul_eq_one
    {I : Type uI} [Fintype I] (x : EuclideanSpace ℂ I) :
    x ∈ Metric.sphere (0 : EuclideanSpace ℂ I) 1 ↔ ∑ i, star (x i) * x i = 1 := by
  have hsum : (∑ i, star (x i) * x i) = inner ℂ x x := by
    calc
      _ = ∑ i, starRingEnd ℂ (x i) * x i := rfl
      _ = inner ℂ x x := by simp only [PiLp.inner_apply, RCLike.inner_apply']
  rw [Metric.mem_sphere, dist_zero_right, hsum]
  constructor
  · exact inner_self_eq_one_of_norm_eq_one
  · intro h
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) x, h]
    simp

end EuclideanSpace
