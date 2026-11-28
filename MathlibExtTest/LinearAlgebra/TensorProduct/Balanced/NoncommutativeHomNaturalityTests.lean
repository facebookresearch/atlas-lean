/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Hom
import Mathlib.Algebra.Module.Opposite
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Noncommutative coordinates for balanced tensor–Hom naturality

Multiplication in the ring of two-by-two integer matrices descends through
balanced tensor–Hom currying. Matrix units witness noncommutativity, zero
products of nonzero factors and a nonzero balanced class. Nonidentity left
multiplication consumes the source and target naturality laws.
-/

noncomputable section

open MulOpposite TensorProduct.Balanced

namespace MathlibExtTest.BalancedHomMatrix

private abbrev M := Matrix (Fin 2) (Fin 2) ℤ
private abbrev Q := Balanced ℤ M M M

private instance : SMulCommClass M Mᵐᵒᵖ M where
  smul_comm a b x := by
    change a * (x * b.unop) = (a * x) * b.unop
    exact (mul_assoc a x b.unop).symm

private instance : Module Mᵐᵒᵖ (CoefficientHom.Hom M M M) :=
  CoefficientHom.homModule M M M M

private instance : Module Mᵐᵒᵖ Q := rightModule ℤ M M M M

private def leftMul (a : M) : M →ₗ[Mᵐᵒᵖ] M where
  toFun x := a * x
  map_add' x y := mul_add a x y
  map_smul' r x := by
    change a * (x * r.unop) = (a * x) * r.unop
    exact (mul_assoc a x r.unop).symm

private def productCurry : M →ₗ[Mᵐᵒᵖ] CoefficientHom.Hom M M M where
  toFun := leftMul
  map_add' x y := by
    ext z
    change (x + y) * z = x * z + y * z
    exact add_mul x y z
  map_smul' r x := by
    ext y
    change leftMul (r • x) y = (r • leftMul x) y
    rw [CoefficientHom.homModule_smul_apply M M M M]
    change (x * r.unop) * y = x * (r.unop * y)
    exact mul_assoc x r.unop y

private def productTensor : Q →ₗ[Mᵐᵒᵖ] M :=
  (CoefficientHom.tensorHomEquiv M M M M M).symm productCurry

private lemma productTensor_mk (x y : M) :
    productTensor (mk ℤ M M M x y) = x * y := by
  exact CoefficientHom.tensorHomEquiv_symm_mk
    (R := M) (S := M) (B := M) (A := M) (C := M) productCurry x y

private def e (i j : Fin 2) : M := fun x y => if x = i ∧ y = j then 1 else 0
private abbrev e00 := e 0 0
private abbrev e01 := e 0 1
private abbrev e10 := e 1 0
private abbrev e11 := e 1 1

private lemma e01_mul_e10 : e01 * e10 = e00 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [e, Matrix.mul_apply, Fin.sum_univ_two]

private lemma e10_mul_e01 : e10 * e01 = e11 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [e, Matrix.mul_apply, Fin.sum_univ_two]

private lemma e00_square : e00 * e00 = e00 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [e, Matrix.mul_apply, Fin.sum_univ_two]

private lemma e10_mul_e00 : e10 * e00 = e10 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [e, Matrix.mul_apply, Fin.sum_univ_two]

private lemma e01_square : e01 * e01 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [e, Matrix.mul_apply, Fin.sum_univ_two]

example : e01 ≠ 0 := by
  intro h
  have hv := congrArg (fun x : M => x 0 1) h
  norm_num [e] at hv

example : productTensor (mk ℤ M M M e01 e10) = e00 := by
  rw [productTensor_mk, e01_mul_e10]

example : productTensor (mk ℤ M M M e10 e01) = e11 := by
  rw [productTensor_mk, e10_mul_e01]

example : e01 ≠ 0 ∧ productTensor (mk ℤ M M M e01 e01) = 0 := by
  constructor
  · intro h
    have hv := congrArg (fun x : M => x 0 1) h
    norm_num [e] at hv
  · rw [productTensor_mk, e01_square]

example : mk ℤ M M M e01 e10 ≠ 0 := by
  intro h
  have hv := congrArg productTensor h
  rw [productTensor_mk, map_zero, e01_mul_e10] at hv
  have hc := congrArg (fun x : M => x 0 0) hv
  norm_num [e] at hc

example : leftMul e01 ≠ (LinearMap.id : M →ₗ[Mᵐᵒᵖ] M) := by
  intro h
  have hv := DFunLike.congr_fun h e10
  have hc := congrArg (fun x : M => x 0 0) hv
  norm_num [leftMul, e, Matrix.mul_apply, Fin.sum_univ_two] at hc

example :
    ((CoefficientHom.tensorHomEquiv M M M M M).symm
      (productCurry.comp (leftMul e01))) (mk ℤ M M M e10 e00) = e00 := by
  rw [CoefficientHom.tensorHomEquiv_naturality_left_symm]
  change productTensor
    (CoefficientHom.tensorMap (R := M) (S := M) (B := M)
      (leftMul e01) (mk ℤ M M M e10 e00)) = e00
  rw [CoefficientHom.tensorMap_mk, productTensor_mk]
  change (e01 * e10) * e00 = e00
  rw [e01_mul_e10, e00_square]

example :
    productTensor (CoefficientHom.tensorMap (R := M) (S := M) (B := M)
      (leftMul e01) (mk ℤ M M M e10 e00)) = e00 := by
  rw [CoefficientHom.tensorMap_mk, productTensor_mk]
  change (e01 * e10) * e00 = e00
  rw [e01_mul_e10, e00_square]

example :
    (CoefficientHom.tensorHomEquiv M M M M M
      ((leftMul e10).comp productTensor)) e01 e10 = e10 ∧
    ((CoefficientHom.map M M M (leftMul e10)).comp
      (CoefficientHom.tensorHomEquiv M M M M M productTensor)) e01 e10 = e10 := by
  have hvalue : (CoefficientHom.tensorHomEquiv M M M M M
      ((leftMul e10).comp productTensor)) e01 e10 = e10 := by
    rw [CoefficientHom.tensorHomEquiv_apply]
    change e10 * productTensor (mk ℤ M M M e01 e10) = e10
    rw [productTensor_mk, e01_mul_e10, e10_mul_e00]
  constructor
  · exact hvalue
  · have h := CoefficientHom.tensorHomEquiv_naturality_right
      (R := M) (S := M) (B := M) productTensor (leftMul e10)
    exact (congrArg (fun F : M →ₗ[Mᵐᵒᵖ] CoefficientHom.Hom M M M => F e01 e10)
      h).symm.trans hvalue

end MathlibExtTest.BalancedHomMatrix
