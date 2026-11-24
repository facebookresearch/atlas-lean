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

public import MathlibExt.Analysis.CStarAlgebra.Module.HilbertAmplification.MatrixCoefficients
public import MathlibExt.Algebra.Star.StarAlgHom
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# The actual finite-frame matrix corner in the full compact tensor

For a finite orthonormal family in the original Hilbert space, send a matrix
to the literal sum of its entries tensor the original rank-one matrix units.
The stock rank-one product/adjoint laws prove its algebra and star fields;
the already constructed tensor matrix coefficients recover every entry.

This injective raw map is the finite-corner prerequisite for comparing each
genuine cross norm in its actual completion. It uses no tensor norm, completed
model, countable Hilbert basis or nontrivial/unit coefficient hypothesis.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators CStarAlgebra TensorProduct

namespace CStarModule.HilbertAmplification

universe uH uA uI

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {ι : Type uI} [Fintype ι]
variable (v : ι → H) (hv : Orthonormal ℂ v)

open scoped Classical in
omit [Fintype ι] in
include hv in
/-- Orthonormal rank-one matrix units have their literal Kronecker multiplication. -/
theorem hilbertCompactRankOne_frame_mul (i j k l : ι) :
    hilbertCompactRankOne H (v i) (v j) * hilbertCompactRankOne H (v k) (v l) =
      if j = k then hilbertCompactRankOne H (v i) (v l) else 0 := by
  rw [hilbertCompactRankOne_mul, (orthonormal_iff_ite.mp hv) j k]
  split_ifs <;> simp only [one_smul, zero_smul]

variable (A : Type uA) [NonUnitalCStarAlgebra A]

/-- The actual finite matrix-entry tensor sum on the original raw algebraic tensor. -/
noncomputable def finiteMatrixTensorLinear :
    CStarMatrix ι ι A →ₗ[ℂ] A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier where
  toFun M := ∑ i, ∑ j, M i j ⊗ₜ[ℂ] hilbertCompactRankOne H (v i) (v j)
  map_add' M N := by
    simp only [CStarMatrix.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]
  map_smul' c M := by
    simp only [RingHom.id_apply, CStarMatrix.smul_apply, Finset.smul_sum,
      TensorProduct.smul_tmul']

/-- Every source matrix has exactly its original finite entry/rank-one tensor sum. -/
theorem finiteMatrixTensorLinear_apply (M : CStarMatrix ι ι A) :
    finiteMatrixTensorLinear v A M =
      ∑ i, ∑ j, M i j ⊗ₜ[ℂ] hilbertCompactRankOne H (v i) (v j) := rfl

open scoped Classical in
omit [Fintype ι] in
include hv in
/-- A product of two original tensor summands obeys the genuine matrix-unit law. -/
theorem finiteMatrixTensor_summand_mul (a b : A) (i j k l : ι) :
    (a ⊗ₜ[ℂ] hilbertCompactRankOne H (v i) (v j)) *
        (b ⊗ₜ[ℂ] hilbertCompactRankOne H (v k) (v l)) =
      if j = k then (a * b) ⊗ₜ[ℂ] hilbertCompactRankOne H (v i) (v l) else 0 := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, hilbertCompactRankOne_frame_mul v hv]
  split_ifs <;> simp only [TensorProduct.tmul_zero]

include hv in
/-- The raw finite tensor sum preserves the original matrix multiplication. -/
theorem finiteMatrixTensorLinear_mul (M N : CStarMatrix ι ι A) :
    finiteMatrixTensorLinear v A (M * N) =
      finiteMatrixTensorLinear v A M * finiteMatrixTensorLinear v A N := by
  classical
  symm
  change (∑ i, ∑ j, M i j ⊗ₜ[ℂ] hilbertCompactRankOne H (v i) (v j)) *
      (∑ k, ∑ l, N k l ⊗ₜ[ℂ] hilbertCompactRankOne H (v k) (v l)) = _
  calc
    _ = ∑ i, ∑ j, ∑ k, ∑ l,
        (M i j ⊗ₜ[ℂ] hilbertCompactRankOne H (v i) (v j)) *
          (N k l ⊗ₜ[ℂ] hilbertCompactRankOne H (v k) (v l)) := by
      simp only [Finset.sum_mul]
      simp only [Finset.mul_sum]
    _ = ∑ i, ∑ j, ∑ k, ∑ l,
        if j = k then (M i j * N k l) ⊗ₜ[ℂ] hilbertCompactRankOne H (v i) (v l) else 0 := by
      simp only [finiteMatrixTensor_summand_mul v hv A]
    _ = ∑ i, ∑ j, ∑ l, ∑ k,
        if j = k then (M i j * N k l) ⊗ₜ[ℂ] hilbertCompactRankOne H (v i) (v l) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ l, (M i j * N j l) ⊗ₜ[ℂ] hilbertCompactRankOne H (v i) (v l) := by
      simp
    _ = ∑ i, ∑ l, ∑ j, (M i j * N j l) ⊗ₜ[ℂ] hilbertCompactRankOne H (v i) (v l) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = finiteMatrixTensorLinear v A (M * N) := by
      simp only [finiteMatrixTensorLinear_apply, CStarMatrix.mul_apply, TensorProduct.sum_tmul]

/-- The raw finite tensor sum preserves the original matrix adjoint. -/
theorem finiteMatrixTensorLinear_star (M : CStarMatrix ι ι A) :
    finiteMatrixTensorLinear v A (star M) = star (finiteMatrixTensorLinear v A M) := by
  simp only [finiteMatrixTensorLinear_apply, CStarMatrix.star_apply,
    star_sum, TensorProduct.star_tmul, hilbertCompactRankOne_star]
  exact Finset.sum_comm

include hv in
/-- Existing full-H tensor coefficients recover every original matrix entry. -/
theorem tensorMatrixCoefficient_finiteMatrixTensor (M : CStarMatrix ι ι A) (i j : ι) :
    tensorMatrixCoefficient H A (v j) (v i) (finiteMatrixTensorLinear v A M) = M i j := by
  classical
  have hi := orthonormal_iff_ite.mp hv
  simp only [finiteMatrixTensorLinear_apply, map_sum, tensorMatrixCoefficient_tmul,
    compactOperatorMatrixCoefficient_apply, hilbertCompactRankOne_coe,
    InnerProductSpace.rankOne_apply, inner_smul_right, hi]
  simp only [ite_mul, mul_ite, one_mul, zero_mul, mul_zero,
    ite_smul, one_smul, zero_smul]
  simp [eq_comm]

include hv in
/-- The original matrix-entry sum is injective, including an empty finite frame. -/
theorem finiteMatrixTensorLinear_injective : Function.Injective (finiteMatrixTensorLinear v A) := by
  intro M N h
  apply CStarMatrix.ext
  intro i j
  have hc := congrArg (tensorMatrixCoefficient H A (v j) (v i)) h
  simpa only [tensorMatrixCoefficient_finiteMatrixTensor v hv A] using hc

/-- The actual nonunital star homomorphism from the original C-star matrix corner. -/
noncomputable def finiteMatrixTensorHom :
    CStarMatrix ι ι A →⋆ₙₐ[ℂ] A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier :=
  NonUnitalStarAlgHom.ofLinearMap (finiteMatrixTensorLinear v A)
    (finiteMatrixTensorLinear_mul v hv A) (finiteMatrixTensorLinear_star v A)

/-- The star hom retains each actual finite matrix-entry tensor sum. -/
theorem finiteMatrixTensorHom_apply (M : CStarMatrix ι ι A) :
    finiteMatrixTensorHom v hv A M =
      ∑ i, ∑ j, M i j ⊗ₜ[ℂ] hilbertCompactRankOne H (v i) (v j) := rfl

/-- The actual finite-frame star homomorphism has the original matrix kernel. -/
theorem finiteMatrixTensorHom_injective : Function.Injective (finiteMatrixTensorHom v hv A) :=
  finiteMatrixTensorLinear_injective v hv A

end CStarModule.HilbertAmplification
