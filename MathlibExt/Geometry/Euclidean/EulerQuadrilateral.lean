/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-- **Euler's quadrilateral theorem.** For any four points $A, B, C, D$ of the Euclidean plane,
write $XY$ for the distance between points $X$ and $Y$, and let $M$ and $N$ be the midpoints of
$AC$ and $BD$. Then
$$AB^2 + BC^2 + CD^2 + DA^2 = AC^2 + BD^2 + 4 MN^2.$$

Proves `Wanted` entry `MetaMathlibExt.euler_quadrilateral` (statement `euler-quadrilateral-s1`).

Source: https://en.wikipedia.org/wiki/Euler%27s_quadrilateral_theorem
-/
theorem MetaMathlibExt.euler_quadrilateral {A B C D : EuclideanSpace ℝ (Fin 2)} :
    dist A B ^ 2 + dist B C ^ 2 + dist C D ^ 2 + dist D A ^ 2 =
      dist A C ^ 2 + dist B D ^ 2 +
        4 * dist ((2 : ℝ)⁻¹ • (A + C)) ((2 : ℝ)⁻¹ • (B + D)) ^ 2 := by
  have e : ∀ p q : EuclideanSpace ℝ (Fin 2), dist p q ^ 2 = inner ℝ (p - q) (p - q) := fun p q => by
    rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
  rw [e A B, e B C, e C D, e D A, e A C, e B D,
    e ((2 : ℝ)⁻¹ • (A + C)) ((2 : ℝ)⁻¹ • (B + D))]
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  rw [real_inner_comm A B, real_inner_comm A C, real_inner_comm B C,
    real_inner_comm A D, real_inner_comm B D, real_inner_comm C D]
  ring
