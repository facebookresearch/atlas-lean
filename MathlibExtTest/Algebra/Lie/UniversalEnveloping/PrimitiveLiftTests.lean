/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: @toskua, Codex
-/
module

import MathlibExt.Algebra.Lie.UniversalEnveloping.PrimitiveLift
import Mathlib.Data.Matrix.Basis
meta import Mathlib.Tactic.NormNum

/-!
# The primitive counit on noncommutative matrix generators

The source is the enveloping algebra of the primitive Lie algebra of the
matrix enveloping algebra. Its canonical primitive counit maps the two
matrix-unit generators and their ordered products to nonzero elements.
The products have different matrix evaluations, and a coproduct cross
coefficient distinguishes the product from the primitive Lie bracket.
-/

noncomputable section

open scoped TensorProduct

namespace MathlibExtTest.UniversalEnvelopingPrimitiveLift

attribute [local instance 100] LieRing.ofAssociativeRing

private abbrev M := Matrix (Fin 2) (Fin 2) ℤ
private abbrev A := UniversalEnvelopingAlgebra ℤ M
private abbrev P := Bialgebra.primitiveLieSubalgebra ℤ A
private abbrev V := UniversalEnvelopingAlgebra ℤ P

private def e01 : M := Matrix.single 0 1 1
private def e10 : M := Matrix.single 1 0 1

private def p01 : P := UniversalEnvelopingAlgebra.ιPrimitive ℤ M e01
private def p10 : P := UniversalEnvelopingAlgebra.ιPrimitive ℤ M e10
private def g01 : V := UniversalEnvelopingAlgebra.ι ℤ p01
private def g10 : V := UniversalEnvelopingAlgebra.ι ℤ p10

private def C : V →ₐc[ℤ] A := UniversalEnvelopingAlgebra.primitiveCounit ℤ A

private def evaluate : A →ₐ[ℤ] M :=
  UniversalEnvelopingAlgebra.lift ℤ (LieHom.id : M →ₗ⁅ℤ⁆ M)

@[simp]
private lemma C_g01 : C g01 = UniversalEnvelopingAlgebra.ι ℤ e01 := by
  change UniversalEnvelopingAlgebra.primitiveCounit ℤ A
    (UniversalEnvelopingAlgebra.ι ℤ p01) = _
  rw [UniversalEnvelopingAlgebra.primitiveCounit_ι]
  rfl

@[simp]
private lemma C_g10 : C g10 = UniversalEnvelopingAlgebra.ι ℤ e10 := by
  change UniversalEnvelopingAlgebra.primitiveCounit ℤ A
    (UniversalEnvelopingAlgebra.ι ℤ p10) = _
  rw [UniversalEnvelopingAlgebra.primitiveCounit_ι]
  rfl

@[simp]
private lemma evaluate_C_g01 : evaluate (C g01) = e01 := by
  rw [C_g01]
  exact UniversalEnvelopingAlgebra.lift_ι_apply ℤ (LieHom.id : M →ₗ⁅ℤ⁆ M) e01

@[simp]
private lemma evaluate_C_g10 : evaluate (C g10) = e10 := by
  rw [C_g10]
  exact UniversalEnvelopingAlgebra.lift_ι_apply ℤ (LieHom.id : M →ₗ⁅ℤ⁆ M) e10

private def entry (i j : Fin 2) : A →ₗ[ℤ] ℤ :=
  (LinearMap.proj j).comp ((LinearMap.proj i).comp evaluate.toLinearMap)

private def crossCoefficient : A ⊗[ℤ] A →ₗ[ℤ] ℤ :=
  (LinearMap.mul' ℤ ℤ).comp (TensorProduct.map (entry 0 1) (entry 1 0))

@[simp]
private lemma crossCoefficient_tmul (a b : A) :
    crossCoefficient (a ⊗ₜ[ℤ] b) = evaluate a 0 1 * evaluate b 1 0 := by
  simp only [crossCoefficient, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.mul'_apply, entry, LinearMap.proj_apply, AlgHom.toLinearMap_apply]

private lemma product_crossCoefficient :
    crossCoefficient (Coalgebra.comul (R := ℤ) (C (g01 * g10))) = 1 := by
  rw [map_mul, C_g01, C_g10]
  change crossCoefficient
    ((Bialgebra.comulAlgHom ℤ A)
      (UniversalEnvelopingAlgebra.ι ℤ e01 * UniversalEnvelopingAlgebra.ι ℤ e10)) = 1
  rw [map_mul]
  change crossCoefficient
    (Coalgebra.comul (R := ℤ) (UniversalEnvelopingAlgebra.ι ℤ e01) *
      Coalgebra.comul (R := ℤ) (UniversalEnvelopingAlgebra.ι ℤ e10)) = 1
  rw [UniversalEnvelopingAlgebra.comul_ι, UniversalEnvelopingAlgebra.comul_ι]
  simp only [add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
    map_add, crossCoefficient_tmul, map_one]
  have h01 : evaluate (UniversalEnvelopingAlgebra.ι ℤ e01) = e01 :=
    UniversalEnvelopingAlgebra.lift_ι_apply ℤ (LieHom.id : M →ₗ⁅ℤ⁆ M) e01
  have h10 : evaluate (UniversalEnvelopingAlgebra.ι ℤ e10) = e10 :=
    UniversalEnvelopingAlgebra.lift_ι_apply ℤ (LieHom.id : M →ₗ⁅ℤ⁆ M) e10
  simp [h01, h10, e01, e10, Matrix.one_apply, Matrix.single_apply]

example : evaluate (C g01) 0 1 = 1 := by simp [e01, Matrix.single_apply]

example : evaluate (C (g01 * g10)) 0 0 = 1 := by
  simp only [map_mul, evaluate_C_g01, evaluate_C_g10, e01, e10,
    Matrix.single_mul_single_same, one_mul]
  norm_num [Matrix.single_apply]

example : evaluate (C (g10 * g01)) 1 1 = 1 := by
  simp only [map_mul, evaluate_C_g01, evaluate_C_g10, e01, e10,
    Matrix.single_mul_single_same, one_mul]
  norm_num [Matrix.single_apply]

example : C (g01 * g10) ≠ C (g10 * g01) := by
  intro h
  have hm := congrArg (fun a : A => evaluate a 0 0) h
  simp only [map_mul, evaluate_C_g01, evaluate_C_g10, e01, e10,
    Matrix.single_mul_single_same, one_mul] at hm
  norm_num [Matrix.single_apply] at hm

example : crossCoefficient (Coalgebra.comul (R := ℤ) (C (g01 * g10))) = 1 :=
  product_crossCoefficient

example : ¬ Bialgebra.IsPrimitiveElem ℤ (C (g01 * g10)) := by
  intro h
  have hc := congrArg crossCoefficient h.comul_eq_tmul_add_tmul
  rw [product_crossCoefficient] at hc
  simp only [map_add, crossCoefficient_tmul, map_one, Matrix.one_apply] at hc
  norm_num at hc

example : evaluate (C (UniversalEnvelopingAlgebra.ι ℤ ⁅p01, p10⁆)) 0 0 = 1 := by
  change evaluate (UniversalEnvelopingAlgebra.primitiveCounit ℤ A
    (UniversalEnvelopingAlgebra.ι ℤ ⁅p01, p10⁆)) 0 0 = 1
  rw [UniversalEnvelopingAlgebra.primitiveCounit_ι]
  change evaluate
    (UniversalEnvelopingAlgebra.ι ℤ e01 * UniversalEnvelopingAlgebra.ι ℤ e10 -
      UniversalEnvelopingAlgebra.ι ℤ e10 * UniversalEnvelopingAlgebra.ι ℤ e01) 0 0 = 1
  simp only [map_sub, map_mul,
    UniversalEnvelopingAlgebra.lift_ι_apply, LieHom.id_apply,
    e01, e10, Matrix.single_mul_single_same, one_mul]
  norm_num [Matrix.single_apply]

example : evaluate (C (HopfAlgebra.antipode ℤ (g01 * g10))) 1 1 = 1 := by
  change evaluate
    (UniversalEnvelopingAlgebra.liftPrimitive ℤ (LieHom.id : P →ₗ⁅ℤ⁆ P)
      (HopfAlgebra.antipode ℤ (g01 * g10))) 1 1 = 1
  rw [UniversalEnvelopingAlgebra.liftPrimitive_antipode]
  change evaluate (HopfAlgebra.antipode ℤ (C (g01 * g10))) 1 1 = 1
  rw [map_mul, C_g01, C_g10, HopfAlgebra.antipode_mul_antidistrib,
    UniversalEnvelopingAlgebra.antipode_ι, UniversalEnvelopingAlgebra.antipode_ι,
    neg_mul_neg]
  simp only [map_mul, UniversalEnvelopingAlgebra.lift_ι_apply, LieHom.id_apply,
    e01, e10, Matrix.single_mul_single_same, one_mul]
  norm_num [Matrix.single_apply]

example : ((UniversalEnvelopingAlgebra.liftPrimitiveEquiv ℤ P A).symm C) p01 = p01 := by
  have h := UniversalEnvelopingAlgebra.primitiveCounit_primitiveLieMap ℤ A
  exact congrArg (fun f : P →ₗ⁅ℤ⁆ P => f p01) h

end MathlibExtTest.UniversalEnvelopingPrimitiveLift
