/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Fintype.BigOperators

/-!
# Orthogonal removal of the vertex mean

Let V be a finite index type and 1 the constant-one vector in ℝ^V. Put P=I-|V|⁻¹11ᵀ; for
nonempty V, Px=x-(∑v x_v/|V|)1. For empty V, the unique vector and matrix are zero. The matrix
P is the orthogonal projection onto {x:∑v x_v=0}. For a symmetric A with A1=0,
(Px)ᵀA(Px)=xᵀAx.

Source: Spielman and Teng, arXiv cs/0607105v5, §3.2.
-/

@[expose] public section

noncomputable section

open Finset Matrix
open scoped BigOperators

namespace Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Projection onto the zero-sum real subspace.**

Let V be a finite index type and 1 the constant-one vector in ℝ^V. Put P=I-|V|⁻¹11ᵀ; for
nonempty V, Px=x-(∑v x_v/|V|)1. For empty V, the unique vector and matrix are zero. The matrix
meanProjection is P, acting by subtracting the unweighted coordinate mean.
-/
def meanProjection : Matrix V V ℝ :=
  1 - (Fintype.card V : ℝ)⁻¹ • vecMulVec (1 : V → ℝ) 1

theorem meanProjection_mulVec (x : V → ℝ) :
    meanProjection *ᵥ x = fun v => x v - (∑ i, x i) / (Fintype.card V : ℝ) := by
  rw [meanProjection, sub_mulVec, one_mulVec, smul_mulVec]
  ext v
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct,
    vecMulVec_apply, Pi.one_apply, one_mul]
  rw [div_eq_mul_inv, mul_comm]

@[simp]
theorem transpose_meanProjection : (meanProjection : Matrix V V ℝ)ᵀ = meanProjection := by
  ext i j
  simp [meanProjection, transpose_apply, Matrix.one_apply, eq_comm]

theorem isHermitian_meanProjection : (meanProjection : Matrix V V ℝ).IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_meanProjection]

@[simp]
theorem meanProjection_mulVec_one : meanProjection *ᵥ (1 : V → ℝ) = 0 := by
  ext v
  have : Nonempty V := ⟨v⟩
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [meanProjection_mulVec, hn]

@[simp]
theorem sum_meanProjection_mulVec (x : V → ℝ) : ∑ v, (meanProjection *ᵥ x) v = 0 := by
  cases isEmpty_or_nonempty V with
  | inl h =>
    let := h
    simp
  | inr h =>
    let := h
    have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp only [meanProjection_mulVec, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
    field_simp
    ring

theorem meanProjection_mulVec_eq_self_iff (x : V → ℝ) :
    meanProjection *ᵥ x = x ↔ ∑ v, x v = 0 := by
  constructor
  · intro h
    have hs := congrArg (fun y : V → ℝ => ∑ v, y v) h
    simpa only [sum_meanProjection_mulVec] using hs.symm
  · intro h
    ext v
    simp [meanProjection_mulVec, h]

@[simp]
theorem meanProjection_mul_self :
    (meanProjection : Matrix V V ℝ) * meanProjection = meanProjection := by
  apply Matrix.ext_of_mulVec_single
  intro v
  rw [← mulVec_mulVec]
  exact (meanProjection_mulVec_eq_self_iff _).mpr (sum_meanProjection_mulVec _)

theorem mul_meanProjection {A : Matrix V V ℝ} (hA : A *ᵥ (1 : V → ℝ) = 0) :
    A * meanProjection = A := by
  rw [meanProjection, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, mul_vecMulVec, hA]
  simp

theorem meanProjection_mul {A : Matrix V V ℝ} (hA : A.IsHermitian)
    (hA1 : A *ᵥ (1 : V → ℝ) = 0) : meanProjection * A = A := by
  have h := congrArg Matrix.conjTranspose (mul_meanProjection hA1)
  simpa only [conjTranspose_mul, isHermitian_meanProjection.eq, hA.eq] using h

omit [DecidableEq V] in
theorem sum_mulVec_eq_zero {A : Matrix V V ℝ} (hA : A.IsHermitian)
    (hA1 : A *ᵥ (1 : V → ℝ) = 0) (x : V → ℝ) : ∑ v, (A *ᵥ x) v = 0 := by
  have ht : Aᵀ = A := (conjTranspose_eq_transpose_of_trivial A).symm.trans hA.eq
  have hrow : (1 : V → ℝ) ᵥ* A = 0 := by
    rw [← mulVec_transpose, ht, hA1]
  have h : (1 : V → ℝ) ⬝ᵥ (A *ᵥ x) = 0 := by
    rw [dotProduct_mulVec, hrow, zero_dotProduct]
  simpa only [dotProduct, Pi.one_apply, one_mul] using h

/-- **Mean removal preserves energy when constants are annihilated.**

Let V be a finite index type and 1 the constant-one vector in ℝ^V. Put P=I-|V|⁻¹11ᵀ; for
nonempty V, Px=x-(∑v x_v/|V|)1. For empty V, the unique vector and matrix are zero. If A is a
real symmetric V×V matrix with A1=0, then (Px)ᵀA(Px)=xᵀAx for every x∈ℝ^V.
-/
theorem meanProjection_energy {A : Matrix V V ℝ} (hA : A.IsHermitian)
    (hA1 : A *ᵥ (1 : V → ℝ) = 0) (x : V → ℝ) :
    (meanProjection *ᵥ x) ⬝ᵥ (A *ᵥ (meanProjection *ᵥ x)) = x ⬝ᵥ (A *ᵥ x) := by
  rw [mulVec_mulVec, mul_meanProjection hA1]
  calc
    (meanProjection *ᵥ x) ⬝ᵥ (A *ᵥ x) =
        x ⬝ᵥ ((meanProjection : Matrix V V ℝ)ᵀ *ᵥ (A *ᵥ x)) :=
      (dotProduct_comm _ _).trans
        (dotProduct_transpose_mulVec meanProjection x (A *ᵥ x)).symm
    _ = x ⬝ᵥ (A *ᵥ x) := by
      rw [transpose_meanProjection, mulVec_mulVec, meanProjection_mul hA hA1]

end Matrix
