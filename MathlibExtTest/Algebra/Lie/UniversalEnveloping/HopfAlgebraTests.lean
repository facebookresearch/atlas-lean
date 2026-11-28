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

public import MathlibExt.Algebra.Lie.UniversalEnveloping.HopfAlgebra
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Reindex
public meta import Mathlib.Tactic.FinCases
public meta import Mathlib.Tactic.NormNum

/-!
# Antipodes on noncommuting integral matrix generators

The universal property evaluates the enveloping algebra of the matrix Lie
algebra in the original matrix algebra. The generators `E₀₁` and `E₁₀` are
nonzero, and their products evaluate to `E₀₀` and `E₁₁` in opposite orders.
The antipode negates a generator and reverses this product. Simultaneously
swapping rows and columns supplies a nonidentity Lie-map naturality square.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open scoped TensorProduct

namespace MathlibExtTest.Algebra.Lie.UniversalEnveloping.HopfAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

private abbrev M := Matrix (Fin 2) (Fin 2) ℤ
private abbrev U := UniversalEnvelopingAlgebra ℤ M

local instance : Module ℤ U := Algebra.toModule

private def e01 : M := Matrix.single 0 1 1
private def e10 : M := Matrix.single 1 0 1

private abbrev g01 : U := UniversalEnvelopingAlgebra.ι ℤ e01
private abbrev g10 : U := UniversalEnvelopingAlgebra.ι ℤ e10

private def evaluate : U →ₐ[ℤ] M :=
  UniversalEnvelopingAlgebra.lift ℤ (LieHom.id : M →ₗ⁅ℤ⁆ M)

@[simp]
private theorem evaluate_ι (x : M) : evaluate (UniversalEnvelopingAlgebra.ι ℤ x) = x :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℤ (LieHom.id : M →ₗ⁅ℤ⁆ M) x

example : HopfAlgebra.antipode ℤ g01 = -g01 :=
  UniversalEnvelopingAlgebra.antipode_ι ℤ M e01

example : evaluate (HopfAlgebra.antipode ℤ g01) 0 1 = -1 := by
  rw [UniversalEnvelopingAlgebra.antipode_ι, map_neg, evaluate_ι]
  norm_num [e01, Matrix.single]

example : g01 ≠ 0 := by
  intro h
  have hv := congrArg (fun a : U => evaluate a 0 1) h
  rw [evaluate_ι, map_zero] at hv
  norm_num [e01, Matrix.single] at hv

private theorem evaluate_product_values :
    evaluate (g01 * g10) 0 0 = 1 ∧ evaluate (g01 * g10) 1 1 = 0 := by
  simp only [map_mul, evaluate_ι]
  constructor <;>
    norm_num [e01, e10, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single]

example : g01 * g10 ≠ 0 := by
  intro h
  have hv := evaluate_product_values.1
  rw [h, map_zero] at hv
  norm_num at hv

private theorem antipode_product :
    HopfAlgebra.antipode ℤ (g01 * g10) = g10 * g01 := by
  rw [HopfAlgebra.antipode_mul_antidistrib,
    UniversalEnvelopingAlgebra.antipode_ι, UniversalEnvelopingAlgebra.antipode_ι,
    neg_mul_neg]

private theorem evaluate_antipode_product_values :
    evaluate (HopfAlgebra.antipode ℤ (g01 * g10)) 0 0 = 0 ∧
      evaluate (HopfAlgebra.antipode ℤ (g01 * g10)) 1 1 = 1 := by
  rw [antipode_product]
  simp only [map_mul, evaluate_ι]
  constructor <;>
    norm_num [e01, e10, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single]

example : HopfAlgebra.antipode ℤ (g01 * g10) ≠ g01 * g10 := by
  intro h
  have hv := congrArg (fun a : U => evaluate a 0 0) h
  rw [evaluate_antipode_product_values.1, evaluate_product_values.1] at hv
  norm_num at hv

example : HopfAlgebra.antipode ℤ (g01 * g10) ≠ 0 := by
  intro h
  have hv := evaluate_antipode_product_values.2
  rw [h, map_zero] at hv
  norm_num at hv

example :
    LinearMap.mul' ℤ U
      ((HopfAlgebra.antipode ℤ).rTensor U (Coalgebra.comul (R := ℤ) (g01 * g10))) = 0 := by
  rw [HopfAlgebra.mul_antipode_rTensor_comul_apply]
  simp only [Bialgebra.counit_mul, g01, g10, UniversalEnvelopingAlgebra.counit_ι,
    zero_mul, map_zero]

example :
    LinearMap.mul' ℤ U
      ((HopfAlgebra.antipode ℤ).lTensor U (Coalgebra.comul (R := ℤ) (g01 * g10))) = 0 := by
  rw [HopfAlgebra.mul_antipode_lTensor_comul_apply]
  simp only [Bialgebra.counit_mul, g01, g10, UniversalEnvelopingAlgebra.counit_ι,
    zero_mul, map_zero]

example : HopfAlgebra.antipode ℤ (HopfAlgebra.antipode ℤ (g01 * g10)) = g01 * g10 :=
  UniversalEnvelopingAlgebra.antipode_antipode ℤ M (g01 * g10)

private def swapLie : M →ₗ⁅ℤ⁆ M :=
  (Matrix.reindexAlgEquiv ℤ ℤ (Equiv.swap (0 : Fin 2) 1)).toAlgHom.toLieHom

private theorem swapLie_e01 : swapLie e01 = e10 := by
  ext i j
  change e01 ((Equiv.swap (0 : Fin 2) 1).symm i)
    ((Equiv.swap (0 : Fin 2) 1).symm j) = e10 i j
  fin_cases i <;> fin_cases j <;> norm_num [e01, e10, Matrix.single]

example :
    UniversalEnvelopingAlgebra.map ℤ swapLie (HopfAlgebra.antipode ℤ g01) =
        HopfAlgebra.antipode ℤ (UniversalEnvelopingAlgebra.map ℤ swapLie g01) ∧
      evaluate (UniversalEnvelopingAlgebra.map ℤ swapLie
        (HopfAlgebra.antipode ℤ g01)) 1 0 = -1 := by
  constructor
  · exact UniversalEnvelopingAlgebra.map_antipode ℤ swapLie g01
  · change evaluate (UniversalEnvelopingAlgebra.map ℤ swapLie
      (HopfAlgebra.antipode ℤ (UniversalEnvelopingAlgebra.ι ℤ e01))) 1 0 = -1
    rw [UniversalEnvelopingAlgebra.map_antipode, UniversalEnvelopingAlgebra.map_ι,
      swapLie_e01, UniversalEnvelopingAlgebra.antipode_ι, map_neg, evaluate_ι]
    norm_num [e10, Matrix.single]

end MathlibExtTest.Algebra.Lie.UniversalEnveloping.HopfAlgebra
