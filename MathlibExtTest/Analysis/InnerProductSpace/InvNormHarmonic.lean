/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.InvNormHarmonic

open Laplacian

/-- A nonzero point, as a helper: `(1, 0, 0)` in Euclidean space. -/
private theorem point_100_ne_zero :
    (WithLp.toLp 2 ![1, 0, 0] : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
  intro h
  have h0 := congrArg WithLp.ofLp h
  simp at h0

/-- A nonzero point, as a helper: `(1, 2, 2)` in Euclidean space. -/
private theorem point_122_ne_zero :
    (WithLp.toLp 2 ![1, 2, 2] : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
  intro h
  have h0 := congrArg WithLp.ofLp h
  simp at h0

/-- Concrete case: at the point `(1, 0, 0)` (nonzero), the Laplacian of
`1 / r` is `0`. -/
example : Δ (fun y : EuclideanSpace ℝ (Fin 3) => ‖y‖⁻¹)
    (WithLp.toLp 2 ![1, 0, 0] : EuclideanSpace ℝ (Fin 3)) = 0 :=
  MathlibExt.Analysis.laplacian_inv_norm_eq_zero point_100_ne_zero

/-- Concrete case: at the point `(1, 2, 2)` (radius `3`), the Laplacian
of `1 / r` is `0`. -/
example : Δ (fun y : EuclideanSpace ℝ (Fin 3) => ‖y‖⁻¹)
    (WithLp.toLp 2 ![1, 2, 2] : EuclideanSpace ℝ (Fin 3)) = 0 :=
  MathlibExt.Analysis.laplacian_inv_norm_eq_zero point_122_ne_zero

/-- The value of `1 / r` at `(1, 2, 2)` is `1 / 3`, so the harmonic
function is nontrivial where its Laplacian vanishes. -/
example : (fun y : EuclideanSpace ℝ (Fin 3) => ‖y‖⁻¹)
    (WithLp.toLp 2 ![1, 2, 2] : EuclideanSpace ℝ (Fin 3)) = 1 / 3 := by
  have hnorm : ‖(WithLp.toLp 2 ![1, 2, 2] : EuclideanSpace ℝ (Fin 3))‖ = 3 := by
    rw [EuclideanSpace.norm_eq]
    have hsum : (∑ i, ‖(WithLp.ofLp
        (WithLp.toLp 2 ![1, 2, 2] : EuclideanSpace ℝ (Fin 3))) i‖ ^ 2) = 9 := by
      simp [Fin.sum_univ_three]
      norm_num
    rw [hsum, show (9 : ℝ) = 3 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  show ‖(WithLp.toLp 2 ![1, 2, 2] : EuclideanSpace ℝ (Fin 3))‖⁻¹ = 1 / 3
  rw [hnorm]
  norm_num
