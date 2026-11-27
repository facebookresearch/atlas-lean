/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.VectorBalancingVolumeBound

namespace MathlibExt.Combinatorics.VectorBalancingVolumeBoundAIMCombinatoricsProblem42Wanted

example : ¬ volumeBoundIsUpperBound := volumeBoundIsUpperBound_refuted

/-- The `ℓ₁` seminorm adds the absolute values of the coordinates. -/
example : l1Seminorm (Fin 3) !₂[3, -4, 0] = 7 := by
  rw [l1Seminorm_apply, Fin.sum_univ_three]
  norm_num

/-- It is not the Euclidean norm of `EuclideanSpace`: `‖(3, 4)‖ = 5`, while the `ℓ₁` norm is `7`. -/
example : ‖!₂[(3 : ℝ), 4]‖ = 5 ∧ l1Seminorm (Fin 2) !₂[3, 4] = 7 := by
  refine ⟨?_, ?_⟩
  · rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, show (5 : ℝ) = √(5 ^ 2) by simp]
    norm_num
  · rw [l1Seminorm_apply, Fin.sum_univ_two]
    norm_num

/-- The seminorm axioms hold with the expected constants: `ℓ₁(a • x) = |a| ℓ₁(x)` and the
triangle inequality. -/
example (x y : EuclideanSpace ℝ (Fin 2)) (a : ℝ) :
    l1Seminorm (Fin 2) (a • x) = |a| * l1Seminorm (Fin 2) x ∧
      l1Seminorm (Fin 2) (x + y) ≤ l1Seminorm (Fin 2) x + l1Seminorm (Fin 2) y :=
  ⟨by rw [map_smul_eq_mul, Real.norm_eq_abs], map_add_le_add _ x y⟩

/-- The `ℓ₁` seminorm is definite, so it is a norm, as the statement requires of `X` and `Y`. -/
example (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) (hx : l1Seminorm (Fin d) x = 0) : x = 0 :=
  l1Seminorm_eq_zero_iff.mp hx

/-- The standard basis vectors lie in the closed `ℓ₁` unit ball. -/
example (d : ℕ) (i : Fin d) : l1Seminorm (Fin d) (EuclideanSpace.single i 1) ≤ 1 := by
  rw [l1Seminorm_single, abs_one]

/-- A signing of `e₁, e₂, e₃`: `‖e₁ - e₂ + e₃‖₁ = 3`. -/
example : l1Seminorm (Fin 3)
    (∑ i, (((![1, -1, 1] : Fin 3 → ℤˣ) i : ℤ) : ℝ) • EuclideanSpace.single i (1 : ℝ)) = 3 := by
  rw [l1Seminorm_sum_smul_single]
  simp

/-- Every signing of the standard basis of `ℝ^d` has `ℓ₁` norm `d`. -/
example (d : ℕ) (ε : Fin d → ℤˣ) :
    l1Seminorm (Fin d) (∑ i, ((ε i : ℤ) : ℝ) • EuclideanSpace.single i (1 : ℝ)) = d := by
  rw [l1Seminorm_sum_smul_single, Fintype.card_fin]

end MathlibExt.Combinatorics.VectorBalancingVolumeBoundAIMCombinatoricsProblem42Wanted
