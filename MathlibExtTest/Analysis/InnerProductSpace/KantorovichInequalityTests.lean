/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.KantorovichInequality

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Matrix.Hermitian

/-!
# Tests for Kantorovich, Bhatia–Davis, and Popoviciu inequalities

Scalar tests use the two-point weights `w = ![1/2, 1/2]` and eigenvalues
`λ = ![1, 4]`, where all three inequalities are equalities (Kantorovich:
`25/16`; Bhatia–Davis and Popoviciu: `9/4`).

Operator tests use the diagonal operators `T = diag(1, 4)` and
`S = diag(1, 1/4)` on `EuclideanSpace ℝ (Fin 2)` at the unit vector
`x = (1/√2, 1/√2)`, where both Rayleigh quotients and the variance are
computed explicitly (`⟪x, T x⟫ = 5/2`, `⟪x, S x⟫ = 5/8`, variance `9/4`).
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.KantorovichInequalityTests

open scoped _root_.InnerProductSpace
open MathlibExt.Analysis.InnerProductSpace.KantorovichInequality

section ScalarTests

private theorem scalar_weights_sum :
    ∑ i, (![1/2, 1/2] : Fin 2 → ℝ) i = 1 := by
  rw [Fin.sum_univ_two]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

private theorem scalar_weights_nonneg :
    ∀ i : Fin 2, 0 ≤ (![1/2, 1/2] : Fin 2 → ℝ) i := by
  rw [Fin.forall_fin_two]
  constructor <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

private theorem scalar_eigenvalues_mem_Icc :
    ∀ i : Fin 2, (1 : ℝ) ≤ (![1, 4] : Fin 2 → ℝ) i ∧ (![1, 4] : Fin 2 → ℝ) i ≤ 4 := by
  rw [Fin.forall_fin_two]
  constructor <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- Kantorovich is an equality for the weights `(1/2, 1/2)` and eigenvalues
`(1, 4)`: both sides are `25/16`. -/
private theorem scalar_kantorovich_equality :
    (∑ i, (![1/2, 1/2] : Fin 2 → ℝ) i * (![1, 4] : Fin 2 → ℝ) i)
        * (∑ i, (![1/2, 1/2] : Fin 2 → ℝ) i / (![1, 4] : Fin 2 → ℝ) i)
      = 25 / 16 := by
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- The scalar Kantorovich theorem applied to the same weights. -/
private theorem scalar_kantorovich_via_theorem :
    (∑ i, (![1/2, 1/2] : Fin 2 → ℝ) i * (![1, 4] : Fin 2 → ℝ) i)
        * (∑ i, (![1/2, 1/2] : Fin 2 → ℝ) i / (![1, 4] : Fin 2 → ℝ) i)
      ≤ (4 + 1) ^ 2 / (4 * 1 * 4) :=
  weighted_kantorovich scalar_weights_nonneg scalar_weights_sum
    (by norm_num) scalar_eigenvalues_mem_Icc

/-- Bhatia–Davis is an equality for the same weights and eigenvalues. -/
private theorem scalar_bhatia_davis_equality :
    (∑ i, (![1/2, 1/2] : Fin 2 → ℝ) i * ((![1, 4] : Fin 2 → ℝ) i) ^ 2)
        - (∑ i, (![1/2, 1/2] : Fin 2 → ℝ) i * (![1, 4] : Fin 2 → ℝ) i) ^ 2
      = 9 / 4 := by
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- Popoviciu's bound is attained for the same weights and eigenvalues. -/
private theorem scalar_popoviciu_equality :
    (∑ i, (![1/2, 1/2] : Fin 2 → ℝ) i * ((![1, 4] : Fin 2 → ℝ) i) ^ 2)
        - (∑ i, (![1/2, 1/2] : Fin 2 → ℝ) i * (![1, 4] : Fin 2 → ℝ) i) ^ 2
      = ((4 - 1) / 2) ^ 2 := by
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  norm_num

/-- The scalar Popoviciu API applied to the same two-point weights. -/
private theorem scalar_popoviciu_via_theorem :
    (∑ i, (![1/2, 1/2] : Fin 2 → ℝ) i * ((![1, 4] : Fin 2 → ℝ) i) ^ 2)
        - (∑ i, (![1/2, 1/2] : Fin 2 → ℝ) i * (![1, 4] : Fin 2 → ℝ) i) ^ 2
      ≤ ((4 - 1) / 2) ^ 2 :=
  weighted_popoviciu scalar_weights_nonneg scalar_weights_sum
    scalar_eigenvalues_mem_Icc

end ScalarTests

section OneDimensionalTests

/-- Kantorovich on `ℝ` with `T = 2 • id`, `S = (1/2) • id`, `x = 1`:
`2 * (1/2) = 1 ≤ 25/16`. -/
private theorem kantorovich_one_dim :
    ⟪(1 : ℝ), ((2 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) (1 : ℝ)⟫_ℝ
        * ⟪(1 : ℝ), ((1 / 2 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) (1 : ℝ)⟫_ℝ
      ≤ (4 + 1) ^ 2 / (4 * 1 * 4) := by
  have hT : (((2 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))).IsSymmetric := by
    intro x y
    simp [RCLike.inner_apply]
    ring
  have hray : ∀ x : ℝ, (1 : ℝ) * ‖x‖ ^ 2 ≤
      ⟪x, ((2 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) x⟫_ℝ ∧
      ⟪x, ((2 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) x⟫_ℝ ≤ (4 : ℝ) * ‖x‖ ^ 2 := by
    intro x
    have hnorm : ‖x‖ ^ 2 = x ^ 2 := by simp [Real.norm_eq_abs, sq_abs]
    have hinner : ⟪x, ((2 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) x⟫_ℝ = 2 * x ^ 2 := by
      simp [RCLike.inner_apply]
      ring
    rw [hnorm, hinner]
    constructor <;> nlinarith [sq_nonneg x]
  have hTS : ∀ x : ℝ, ((2 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))
      ((((1 / 2 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))) x) = x := by
    intro x
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    ring
  have hST : ∀ x : ℝ, (((1 / 2 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)))
      (((2 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) x) = x := by
    intro x
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    ring
  have h := kantorovich_inequality hT (1 : ℝ)
    (by simp : ‖(1 : ℝ)‖ = 1) hray (by norm_num : (0 : ℝ) < 1) hTS hST
  exact h

end OneDimensionalTests

section TwoDimensionalTests

/-- The diagonal operator with diagonal `d` on `EuclideanSpace ℝ (Fin 2)`. -/
private noncomputable def diagOp (d : Fin 2 → ℝ) :
    EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Matrix.toEuclideanLin (Matrix.diagonal d)

/-- Applying a diagonal operator multiplies coordinatewise. -/
private theorem diagOp_apply (d : Fin 2 → ℝ) (x : EuclideanSpace ℝ (Fin 2))
    (i : Fin 2) : (diagOp d x) i = d i * x i := by
  simp [diagOp, Matrix.toLpLin_apply, Matrix.mulVec_diagonal]

/-- The Rayleigh quotient of a diagonal operator. -/
private theorem diagOp_rayleigh (d : Fin 2 → ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    ⟪x, diagOp d x⟫_ℝ = ∑ i, d i * (x i) ^ 2 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [diagOp_apply]
  simp [RCLike.inner_apply]
  ring

/-- The second-moment quadratic form of a diagonal operator. -/
private theorem diagOp_second_moment (d : Fin 2 → ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    ⟪x, diagOp d (diagOp d x)⟫_ℝ = ∑ i, (d i) ^ 2 * (x i) ^ 2 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [diagOp_apply, diagOp_apply]
  simp [RCLike.inner_apply]
  ring

private theorem diag_symm (d : Fin 2 → ℝ) : (diagOp d).IsSymmetric :=
  (Matrix.isSymmetric_toEuclideanLin_iff).mpr (Matrix.isHermitian_diagonal d)

/-- The diagonal operator `diag(1, 4)` has Rayleigh quotients in `[1, 4]`. -/
private theorem diag_rayleigh_bounds :
    ∀ x : EuclideanSpace ℝ (Fin 2),
      (1 : ℝ) * ‖x‖ ^ 2 ≤ ⟪x, diagOp ![1, 4] x⟫_ℝ ∧
        ⟪x, diagOp ![1, 4] x⟫_ℝ ≤ (4 : ℝ) * ‖x‖ ^ 2 := by
  intro x
  rw [diagOp_rayleigh, EuclideanSpace.real_norm_sq_eq]
  have hd1 : ∀ i : Fin 2, (1 : ℝ) ≤ (![1, 4] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have hd4 : ∀ i : Fin 2, (![1, 4] : Fin 2 → ℝ) i ≤ 4 := by
    intro i
    fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  constructor
  · rw [one_mul]
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_right (hd1 i) (sq_nonneg (x i))
    simpa using h
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_right (hd4 i) (sq_nonneg (x i))
    simpa using h

/-- The two diagonal operators are two-sided inverses of each other. -/
private theorem diag_inverse_left :
    ∀ x : EuclideanSpace ℝ (Fin 2),
      diagOp ![1, 4] (diagOp ![1, 1 / 4] x) = x := by
  intro x
  apply PiLp.ext
  rw [Fin.forall_fin_two]
  constructor <;> rw [diagOp_apply, diagOp_apply] <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]

private theorem diag_inverse_right :
    ∀ x : EuclideanSpace ℝ (Fin 2),
      diagOp ![1, 1 / 4] (diagOp ![1, 4] x) = x := by
  intro x
  apply PiLp.ext
  rw [Fin.forall_fin_two]
  constructor <;> rw [diagOp_apply, diagOp_apply] <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The test unit vector `(1/√2, 1/√2)`. -/
private noncomputable def testVec : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (![1 / Real.sqrt 2, 1 / Real.sqrt 2] : Fin 2 → ℝ)

private theorem testVec_norm : ‖testVec‖ = 1 := by
  have h2 : ‖testVec‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have hcoord : ∀ i : Fin 2, (testVec i) ^ 2 = 1 / 2 := by
      intro i
      fin_cases i <;>
        simp [testVec, Matrix.cons_val_zero, Matrix.cons_val_one,
          Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Fin.sum_univ_two, hcoord 0, hcoord 1]
    norm_num
  have hnn : 0 ≤ ‖testVec‖ := norm_nonneg _
  rcases sq_eq_one_iff.mp h2 with h | h
  · exact h
  · linarith

private theorem testVec_rayleigh :
    ⟪testVec, diagOp ![1, 4] testVec⟫_ℝ = 5 / 2 := by
  rw [diagOp_rayleigh, Fin.sum_univ_two]
  have hcoord : ∀ i : Fin 2, (testVec i) ^ 2 = 1 / 2 := by
    intro i
    fin_cases i <;>
      simp [testVec, Matrix.cons_val_zero, Matrix.cons_val_one,
          Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hcoord 0, hcoord 1]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

private theorem testVec_rayleigh_inv :
    ⟪testVec, diagOp ![1, 1 / 4] testVec⟫_ℝ = 5 / 8 := by
  rw [diagOp_rayleigh, Fin.sum_univ_two]
  have hcoord : ∀ i : Fin 2, (testVec i) ^ 2 = 1 / 2 := by
    intro i
    fin_cases i <;>
      simp [testVec, Matrix.cons_val_zero, Matrix.cons_val_one,
          Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hcoord 0, hcoord 1]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- Kantorovich for `diag(1, 4)` at `(1/√2, 1/√2)`: `(5/2) * (5/8) = 25/16`,
the bound. -/
private theorem kantorovich_diag_test :
    ⟪testVec, diagOp ![1, 4] testVec⟫_ℝ
        * ⟪testVec, diagOp ![1, 1 / 4] testVec⟫_ℝ
      ≤ (4 + 1) ^ 2 / (4 * 1 * 4) := by
  have h := kantorovich_inequality (T := diagOp ![1, 4]) (S := diagOp ![1, 1 / 4])
    (diag_symm ![1, 4]) testVec testVec_norm diag_rayleigh_bounds
    (by norm_num : (0 : ℝ) < (1 : ℝ)) diag_inverse_left diag_inverse_right
  exact h

/-- Bhatia–Davis for `diag(1, 4)` at `(1/√2, 1/√2)`: variance `9/4` against
the bound `(4 - 5/2) * (5/2 - 1) = 9/4`. -/
private theorem bhatia_davis_diag_test :
    ⟪testVec, diagOp ![1, 4] (diagOp ![1, 4] testVec)⟫_ℝ
        - ⟪testVec, diagOp ![1, 4] testVec⟫_ℝ ^ 2
      ≤ (4 - ⟪testVec, diagOp ![1, 4] testVec⟫_ℝ)
        * (⟪testVec, diagOp ![1, 4] testVec⟫_ℝ - 1) := by
  exact bhatia_davis_inequality (T := diagOp ![1, 4]) (diag_symm ![1, 4])
    testVec testVec_norm diag_rayleigh_bounds

/-- The operator Popoviciu API at the same diagonal operator and unit vector. -/
private theorem popoviciu_diag_test :
    ⟪testVec, diagOp ![1, 4] (diagOp ![1, 4] testVec)⟫_ℝ
        - ⟪testVec, diagOp ![1, 4] testVec⟫_ℝ ^ 2
      ≤ ((4 - 1) / 2) ^ 2 := by
  exact popoviciu_inequality (T := diagOp ![1, 4]) (diag_symm ![1, 4])
    testVec testVec_norm diag_rayleigh_bounds

/-- The variance at the test vector is exactly `9/4`. -/
private theorem variance_diag_test :
    ⟪testVec, diagOp ![1, 4] (diagOp ![1, 4] testVec)⟫_ℝ
        - ⟪testVec, diagOp ![1, 4] testVec⟫_ℝ ^ 2 = 9 / 4 := by
  rw [diagOp_second_moment, testVec_rayleigh, Fin.sum_univ_two]
  have hcoord : ∀ i : Fin 2, (testVec i) ^ 2 = 1 / 2 := by
    intro i
    fin_cases i <;>
      simp [testVec, Matrix.cons_val_zero, Matrix.cons_val_one,
          Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hcoord 0, hcoord 1]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

end TwoDimensionalTests

end MathlibExt.Analysis.InnerProductSpace.KantorovichInequalityTests
