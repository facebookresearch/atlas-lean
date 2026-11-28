/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
import MathlibExt.LinearAlgebra.TensorProduct.AlgebraTensorHom
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Left algebra action in Hom-tensor cancellation

The target algebra is the noncommutative ring of two-by-two matrices over
ZMod 6. Multiplication by the first matrix unit gives the first diagonal
coordinate; right multiplication would instead give the second coordinate.
-/

noncomputable section
open scoped TensorProduct
namespace AlgebraTensorHomTests
private abbrev A := Matrix (Fin 2) (Fin 2) (ZMod 6)
private abbrev e01 : A := Matrix.single 0 1 1
private abbrev e10 : A := Matrix.single 1 0 1
private def f : ℤ →ₗ[ℤ] A := LinearMap.toSpanSingleton ℤ A e10

example :
    ((TensorProduct.algebraTensorHomEquiv ℤ A ℤ A).symm f
      (e01 ⊗ₜ[ℤ] (1 : ℤ))) 0 0 = 1 ∧
    ((TensorProduct.algebraTensorHomEquiv ℤ A ℤ A).symm f
      (e01 ⊗ₜ[ℤ] (1 : ℤ))) 1 1 = 0 := by
  rw [TensorProduct.algebraTensorHomEquiv_symm_tmul]
  norm_num [f, e01, e10, LinearMap.toSpanSingleton_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_succ]

example :
    ((TensorProduct.algebraTensorHomEquiv ℤ A ℤ A).symm f
      (e01 ⊗ₜ[ℤ] (2 : ℤ))) 0 0 = 2 ∧ (2 : ZMod 6) ≠ 0 := by
  rw [TensorProduct.algebraTensorHomEquiv_symm_tmul]
  norm_num [f, e01, e10, LinearMap.toSpanSingleton_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_succ]
end AlgebraTensorHomTests
