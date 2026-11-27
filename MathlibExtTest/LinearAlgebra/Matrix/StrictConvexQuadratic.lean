/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.StrictConvexQuadratic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for real matrix quadratics

The identity is positive definite. The rank-one diagonal matrix with diagonal `(2, 0)`
is singular positive semidefinite, with different behavior for right-hand sides `(4, 0)`
and `(0, 1)`.
-/

namespace MathlibExtTest.StrictConvexQuadratic

open Filter Matrix MetaMathlibExt.Matrix

example : StrictConvexOn ℝ Set.univ
    (fun x : Fin 2 → ℝ ↦ x ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ x)) :=
  strictConvexOn_quadratic_of_posDef Matrix.PosDef.one

example (x y : Fin 2 → ℝ) (a b : ℝ) (hab : a + b = 1) :
    a * (x ⬝ᵥ x) + b * (y ⬝ᵥ y) - ((a • x + b • y) ⬝ᵥ (a • x + b • y)) =
      a * b * ((x - y) ⬝ᵥ (x - y)) := by
  have hI : (1 : Matrix (Fin 2) (Fin 2) ℝ).IsHermitian := Matrix.isHermitian_one
  simpa only [one_mulVec] using quadratic_jensen_gap hI.isSymm x y a b hab

example (x : Fin 2 → ℝ) :
    IsMinOn (fun y : Fin 2 → ℝ ↦ y ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ y) -
      2 * ((![1, 2] : Fin 2 → ℝ) ⬝ᵥ y)) Set.univ x ↔ x = ![1, 2] := by
  simpa only [one_mulVec] using
    isMinOn_quadratic_sub_linear_iff (Matrix.PosDef.one (n := Fin 2) (R := ℝ)).posSemidef ![1, 2] x

private def A : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![2, 0]

private lemma hA : A.PosSemidef := by
  rw [A, Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num

private lemma hdet : A.det = 0 := by
  simp [A, Matrix.det_diagonal, Fin.prod_univ_two]

example : ConvexOn ℝ Set.univ (fun x ↦ x ⬝ᵥ (A *ᵥ x)) :=
  convexOn_quadratic_of_posSemidef hA

example : ¬ StrictConvexOn ℝ Set.univ (fun x ↦ x ⬝ᵥ (A *ᵥ x)) :=
  not_strictConvexOn_quadratic_of_det_eq_zero hdet

-- In the null direction, the quadratic stays constant even away from a minimizer.
example (x : Fin 2 → ℝ) :
    (x + ![0, 1]) ⬝ᵥ (A *ᵥ (x + ![0, 1])) = x ⬝ᵥ (A *ᵥ x) := by
  apply quadratic_add_of_mulVec_eq_zero hA.isHermitian.isSymm
  ext i
  fin_cases i <;> norm_num [A, mulVec_diagonal]

-- The entire minimizing set for the consistent system is the line `x 0 = 2`.
private lemma consistent_iff (x : Fin 2 → ℝ) :
    IsMinOn (fun y ↦ y ⬝ᵥ (A *ᵥ y) - 2 * ((![4, 0] : Fin 2 → ℝ) ⬝ᵥ y)) Set.univ x ↔
      x 0 = 2 := by
  rw [isMinOn_quadratic_sub_linear_iff hA]
  constructor
  · intro hx
    have h := congrFun hx 0
    norm_num [A, mulVec_diagonal] at h
    linarith
  · intro hx
    ext i
    fin_cases i <;> norm_num [A, mulVec_diagonal, hx]

example : ∃ y, y ≠ (![2, 0] : Fin 2 → ℝ) ∧
    IsMinOn (fun z ↦ z ⬝ᵥ (A *ᵥ z) - 2 * ((![4, 0] : Fin 2 → ℝ) ⬝ᵥ z)) Set.univ y :=
  exists_ne_isMinOn_quadratic_sub_linear_of_det_eq_zero hA hdet ((consistent_iff _).2 rfl)

private lemma inconsistent : (![0, 1] : Fin 2 → ℝ) ∉ Set.range A.mulVec := by
  rintro ⟨x, hx⟩
  have h := congrFun hx 1
  norm_num [A, mulVec_diagonal] at h

example : ¬ ∃ x,
    IsMinOn (fun y ↦ y ⬝ᵥ (A *ᵥ y) - 2 * ((![0, 1] : Fin 2 → ℝ) ⬝ᵥ y)) Set.univ x :=
  (exists_isMinOn_quadratic_sub_linear_iff hA _).not.mpr inconsistent

-- For the inconsistent system the API gives a descent ray, not just nonattainment.
example : ∃ v : Fin 2 → ℝ, A *ᵥ v = 0 ∧ 0 < (![0, 1] : Fin 2 → ℝ) ⬝ᵥ v ∧
    Tendsto (fun t : ℝ ↦ (t • v) ⬝ᵥ (A *ᵥ (t • v)) -
      2 * ((![0, 1] : Fin 2 → ℝ) ⬝ᵥ (t • v))) atTop atBot :=
  exists_tendsto_quadratic_sub_linear_atBot_of_not_mem_range hA.isHermitian.isSymm inconsistent

end MathlibExtTest.StrictConvexQuadratic
