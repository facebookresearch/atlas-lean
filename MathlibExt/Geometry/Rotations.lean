/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Sphere geometry and rotations: the angular-velocity matrix

For a curve `R(t)` of orthogonal matrices, the angular-velocity matrix
`W(t) = R'(t) R(t)ᵀ` is skew-symmetric, and a rotated vector
`r(t) = R(t) a` satisfies `r' = W r`.

## i. Overview

`R'(t)` is the entrywise `deriv`. Skew-symmetry comes from
differentiating the entrywise orthogonality identity
`∑ k, R(t) i k * R(t) j k = δ i j` (constant in `t`) with the product
rule. The rotated-vector formula expands `W r` and collapses the double
sum with the column orthogonality `∑ j, R(t) j k * R(t) j l = δ k l`,
which follows from `R Rᵀ = 1` via `mul_eq_one_comm`. This is the vector
(not affine-point) statement; affine physical position uses an explicit
origin/chart. No `SO(3)` restriction is needed for skew-symmetry.

## ii. Key results

- `EarthScience.angular_velocity_skew`: `W i j = -W j i`.
- `EarthScience.rotated_vector_deriv`: `r' = W r` entrywise.

## iii. Table of contents

- A. Skew-symmetry of the angular-velocity matrix
- B. Derivative of a rotated vector

## iv. References

- `deriv_fun_sum`, `deriv_mul`, `mul_eq_one_comm` (Mathlib).

## A. Skew-symmetry of the angular-velocity matrix
-/

@[expose] public section

namespace EarthScience

/-- Angular-velocity matrix is skew-symmetric: if `R(t)` is orthogonal
(`R(t) * R(t)ᵀ = 1`) and every entry is differentiable at `t`, then the
matrix `W` with entries `W i j = ∑ k, R'(t) i k * R(t) j k` satisfies
`W i j = -W j i`. Here `R'` is the entrywise `deriv`. -/
theorem angular_velocity_skew {n : ℕ} (R : ℝ → Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (hOrth : ∀ s, R s * Matrix.transpose (R s) = 1)
    (hDiff : ∀ i k, DifferentiableAt ℝ (fun s => R s i k) t) :
    ∀ i j, (∑ k, deriv (fun s => R s i k) t * R t j k)
      = -(∑ k, deriv (fun s => R s j k) t * R t i k) := by
  intro i j
  have hEntry : ∀ s : ℝ, (∑ k, R s i k * R s j k)
      = (if i = j then (1 : ℝ) else 0) := by
    intro s
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) (hOrth s)
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h
  have hderiv : deriv (fun s => ∑ k, R s i k * R s j k) t
      = ∑ k, (deriv (fun s => R s i k) t * R t j k
        + R t i k * deriv (fun s => R s j k) t) := by
    have hdiff : ∀ k ∈ Finset.univ,
        DifferentiableAt ℝ (fun s => R s i k * R s j k) t :=
      fun k _ => (hDiff i k).mul (hDiff j k)
    rw [deriv_fun_sum hdiff]
    apply Finset.sum_congr rfl
    intro k _
    exact deriv_mul (hDiff i k) (hDiff j k)
  have hzero : deriv (fun s => ∑ k, R s i k * R s j k) t = 0 := by
    have hfun : (fun s => ∑ k, R s i k * R s j k)
        = (fun _ => if i = j then (1 : ℝ) else 0) := funext hEntry
    rw [hfun]
    exact deriv_const t _
  have h0 : (∑ k, deriv (fun s => R s i k) t * R t j k)
      + (∑ k, deriv (fun s => R s j k) t * R t i k) = 0 := by
    have h := hderiv.symm.trans hzero
    rw [Finset.sum_add_distrib] at h
    have hcomm : (∑ k, R t i k * deriv (fun s => R s j k) t)
        = ∑ k, deriv (fun s => R s j k) t * R t i k :=
      Finset.sum_congr rfl (fun k _ => mul_comm _ _)
    rw [hcomm] at h
    exact h
  exact eq_neg_of_add_eq_zero_left h0

/-! ## B. Derivative of a rotated vector -/

/-- Rotated-vector derivative: for a fixed vector `a`, the derivative of
`r(t) = R(t) *ᵥ a` at `t` equals `W r(t)`, where `W i j =
∑ k, R'(t) i k * R(t) j k` is the angular-velocity matrix. -/
theorem rotated_vector_deriv {n : ℕ} (R : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) (t : ℝ) (i : Fin n)
    (hOrth : ∀ s, R s * Matrix.transpose (R s) = 1)
    (hDiff : ∀ i k, DifferentiableAt ℝ (fun s => R s i k) t) :
    deriv (fun s => Matrix.mulVec (R s) a i) t
      = ∑ j, (∑ k, deriv (fun s => R s i k) t * R t j k)
          * Matrix.mulVec (R t) a j := by
  have hCol : ∀ k l : Fin n, (∑ j, R t j k * R t j l)
      = (if k = l then (1 : ℝ) else 0) := by
    intro k l
    have hT : Matrix.transpose (R t) * R t = 1 := mul_eq_one_comm.mp (hOrth t)
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M k l) hT
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h
  have hCollapse : ∀ k l : Fin n,
      (∑ j, (deriv (fun s => R s i k) t * R t j k) * (R t j l * a l))
      = (if k = l then deriv (fun s => R s i k) t * a l else 0) := by
    intro k l
    have hfac : (∑ j, (deriv (fun s => R s i k) t * R t j k) * (R t j l * a l))
        = (deriv (fun s => R s i k) t * a l) * (∑ j, R t j k * R t j l) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hfac, hCol k l]
    by_cases h : k = l <;> simp [h]
  have hLHS : deriv (fun s => Matrix.mulVec (R s) a i) t
      = ∑ k, deriv (fun s => R s i k) t * a k := by
    have hfun : (fun s => Matrix.mulVec (R s) a i)
        = (fun s => ∑ k, R s i k * a k) := by
      funext s
      exact Matrix.mulVec_apply_eq_sum (R s) a i
    have hdiff : ∀ k ∈ Finset.univ,
        DifferentiableAt ℝ (fun s => R s i k * a k) t :=
      fun k _ => (hDiff i k).mul_const (a k)
    rw [hfun, deriv_fun_sum hdiff]
    apply Finset.sum_congr rfl
    intro k _
    exact deriv_mul_const (hDiff i k) (a k)
  rw [hLHS]
  simp_rw [Matrix.mulVec_apply_eq_sum]
  simp_rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  simp_rw [hCollapse k]
  simp [Finset.sum_ite_eq]

end EarthScience
