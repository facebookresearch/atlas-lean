/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoefficientComplex
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public meta import Mathlib.Tactic.NormNum

/-!
# Nonzero adjoint coefficients in the canonical CE complex

The commutator Lie algebra of integer two-by-two matrices acts on itself.
The first coefficient differential retains its negative action sign. A matrix
coordinate detects a nonzero second boundary, while the actual constructed
coefficient complex proves that the consecutive differentials compose to zero.
-/

noncomputable section

open CategoryTheory ChevalleyEilenberg
open scoped TensorProduct

namespace MathlibExtTest.CanonicalCoefficient

private abbrev Mat := Matrix (Fin 2) (Fin 2) ℤ
private abbrev E := ExteriorAlgebra ℤ Mat
local instance : LieRing Mat := LieRing.ofAssociativeRing
local instance : LieAlgebra ℤ Mat := LieAlgebra.ofAssociativeAlgebra
local instance : LieRingModule Mat Mat := lieRingSelfModule
local instance : LieModule ℤ Mat Mat := lieAlgebraSelfModule
private abbrev K := coefficientComplex ℤ Mat Mat
private def e01 : Mat := !![0, 1; 0, 0]
private def e10 : Mat := !![0, 0; 1, 0]
private def diagonal : Mat := !![1, 0; 0, -1]
private def pairInputs : Fin 2 → Mat := ![e01, e10]
private lemma bracket_pair : ⁅e01, e10⁆ = diagonal := by
  change e01 * e10 - e10 * e01 = diagonal
  decide
private lemma bracket_reverse : ⁅e10, e01⁆ = -diagonal := by
  change e10 * e01 - e01 * e10 = -diagonal
  decide
private def oneWord (x : Mat) : ⋀[ℤ]^1 Mat := exteriorPower.ιMulti ℤ 1 (fun _ => x)
private def pair : ⋀[ℤ]^2 Mat := exteriorPower.ιMulti ℤ 2 pairInputs
private def zeroWord : ⋀[ℤ]^0 Mat := exteriorPower.ιMulti ℤ 0 Fin.elim0
@[simp] private lemma oneWord_coe (x : Mat) : (oneWord x : E) = ExteriorAlgebra.ι ℤ x := by
  simp [oneWord, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply]
private lemma pair_coe : (pair : E) = ExteriorAlgebra.ι ℤ e01 * ExteriorAlgebra.ι ℤ e10 := by
  simp [pair, pairInputs, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply]
private def entry (i j : Fin 2) : Mat →ₗ[ℤ] ℤ :=
  (LinearMap.proj j : (Fin 2 → ℤ) →ₗ[ℤ] ℤ).comp
    ((LinearMap.proj i : (Fin 2 → Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ)).comp
      (Matrix.ofLinearEquiv ℤ).symm.toLinearMap)
@[simp] private lemma entry_apply (i j : Fin 2) (a : Mat) : entry i j a = a i j := rfl
private def degreeOneProjection : E →ₗ[ℤ] ⋀[ℤ]^1 Mat :=
  (DirectSum.component ℤ ℕ (fun n => ↥(⋀[ℤ]^n Mat)) 1).comp
    (DirectSum.decomposeLinearEquiv (fun n : ℕ => ⋀[ℤ]^n Mat)).toLinearMap
@[simp] private lemma degreeOneProjection_subtype (a : ⋀[ℤ]^1 Mat) :
    degreeOneProjection (a : E) = a := by
  change DirectSum.decompose (fun n : ℕ => ⋀[ℤ]^n Mat) (a : E) 1 = a
  rw [DirectSum.decompose_coe, DirectSum.of_eq_same]
private def firstEntry : E →ₗ[ℤ] ℤ := (entry 0 0).comp
  ((exteriorPower.oneEquiv ℤ Mat).toLinearMap.comp (degreeOneProjection))
@[simp] private lemma firstEntry_ι (x : Mat) : firstEntry (ExteriorAlgebra.ι ℤ x) = x 0 0 := by
  change (exteriorPower.oneEquiv ℤ Mat (degreeOneProjection
    (ExteriorAlgebra.ι ℤ x))) 0 0 = x 0 0
  rw [← oneWord_coe x, degreeOneProjection_subtype]
  simp [oneWord]
private def readZero : ((⋀[ℤ]^0 Mat) ⊗[ℤ] Mat) →ₗ[ℤ] Mat :=
  (TensorProduct.lid ℤ Mat).toLinearMap.comp
    (TensorProduct.map (exteriorPower.zeroEquiv ℤ Mat).toLinearMap LinearMap.id)
private def readOne : (E ⊗[ℤ] Mat) →ₗ[ℤ] ℤ :=
  (TensorProduct.lid ℤ ℤ).toLinearMap.comp (TensorProduct.map firstEntry (entry 0 1))
@[simp] private lemma readZero_zeroWord_tmul (m : Mat) : readZero (zeroWord ⊗ₜ[ℤ] m) = m := by
  change TensorProduct.lid ℤ Mat
    (TensorProduct.map (exteriorPower.zeroEquiv ℤ Mat).toLinearMap LinearMap.id
      (zeroWord ⊗ₜ[ℤ] m)) = m
  rw [TensorProduct.map_tmul]
  change TensorProduct.lid ℤ Mat
    ((exteriorPower.zeroEquiv ℤ Mat zeroWord) ⊗ₜ[ℤ] m) = m
  have h : exteriorPower.zeroEquiv ℤ Mat zeroWord = 1 := by simp [zeroWord]
  rw [h, TensorProduct.lid_tmul, one_smul]
@[simp] private lemma readOne_ι_tmul (a b : Mat) :
    readOne (ExteriorAlgebra.ι ℤ a ⊗ₜ[ℤ] b) = a 0 0 * b 0 1 := by
  change TensorProduct.lid ℤ ℤ
    (TensorProduct.map firstEntry (entry 0 1) (ExteriorAlgebra.ι ℤ a ⊗ₜ[ℤ] b)) =
      a 0 0 * b 0 1
  rw [TensorProduct.map_tmul]
  change TensorProduct.lid ℤ ℤ
    (firstEntry (ExteriorAlgebra.ι ℤ a) ⊗ₜ[ℤ] entry 0 1 b) = _
  rw [firstEntry_ι, TensorProduct.lid_tmul, entry_apply]
  rfl
private lemma firstBoundary : (K.d 1 0).hom (oneWord e01 ⊗ₜ[ℤ] e10) =
    -(zeroWord ⊗ₜ[ℤ] diagonal) := by
  rw [coefficientComplex_d_succ]
  exact (coefficientDifferential_ι_tmul ℤ Mat Mat e01 e10).trans
    (congrArg (fun x : Mat => -(zeroWord ⊗ₜ[ℤ] x)) bracket_pair)
private lemma firstValue : readZero ((K.d 1 0).hom (oneWord e01 ⊗ₜ[ℤ] e10)) =
    -diagonal := by
  rw [firstBoundary, LinearMap.map_neg, readZero_zeroWord_tmul]
example : ⁅e01, e10⁆ ≠ 0 := by
  rw [bracket_pair]
  exact (by decide : diagonal ≠ 0)
example : readZero ((K.d 1 0).hom (oneWord e01 ⊗ₜ[ℤ] e10)) = -diagonal := firstValue
example : (K.d 1 0).hom (oneWord e01 ⊗ₜ[ℤ] e10) ≠ 0 := by
  intro hz
  have h : (-diagonal : Mat) = 0 := firstValue.symm.trans
    ((congrArg (fun z : (⋀[ℤ]^0 Mat) ⊗[ℤ] Mat => readZero z) hz).trans
      (show readZero (0 : (⋀[ℤ]^0 Mat) ⊗[ℤ] Mat) = 0 from readZero.map_zero))
  exact (by decide : (-diagonal : Mat) ≠ 0) h
private lemma boundary_pair : coefficientBoundary ℤ Mat Mat
    ((ExteriorAlgebra.ι ℤ e01 * ExteriorAlgebra.ι ℤ e10) ⊗ₜ[ℤ] e01) =
    -(ExteriorAlgebra.ι ℤ diagonal ⊗ₜ[ℤ] e01) -
      ExteriorAlgebra.ι ℤ e01 ⊗ₜ[ℤ] diagonal := by
  rw [coefficientBoundary_ι_mul_tmul, coefficientDiagonalAction_tmul,
    adjointAction_ι, coefficientBoundary_ι_tmul, bracket_pair]
  simp only [lie_self, TensorProduct.tmul_zero, add_zero, map_neg,
    coefficientInsertion_tmul, mul_one, bracket_reverse, TensorProduct.tmul_neg,
    neg_neg, sub_neg_eq_add, ← sub_eq_add_neg]
private lemma secondAmbient : ((⋀[ℤ]^1 Mat).subtype.rTensor Mat)
    ((K.d 2 1).hom (pair ⊗ₜ[ℤ] e01)) =
    -(ExteriorAlgebra.ι ℤ diagonal ⊗ₜ[ℤ] e01) -
      ExteriorAlgebra.ι ℤ e01 ⊗ₜ[ℤ] diagonal := by
  rw [coefficientComplex_d_succ]
  change ((⋀[ℤ]^1 Mat).subtype.rTensor Mat)
    (coefficientDifferential ℤ Mat Mat 1 (pair ⊗ₜ[ℤ] e01)) = _
  rw [coefficientDifferential_inclusion_apply]
  simpa only [LinearMap.rTensor_tmul, Submodule.subtype_apply, pair_coe] using boundary_pair
private lemma secondValue : readOne (((⋀[ℤ]^1 Mat).subtype.rTensor Mat)
    ((K.d 2 1).hom (pair ⊗ₜ[ℤ] e01))) = -1 := by
  rw [secondAmbient, LinearMap.map_sub, LinearMap.map_neg,
    readOne_ι_tmul, readOne_ι_tmul]
  norm_num [diagonal, e01]
example : readOne (((⋀[ℤ]^1 Mat).subtype.rTensor Mat)
    ((K.d 2 1).hom (pair ⊗ₜ[ℤ] e01))) = -1 := secondValue
example : (K.d 2 1).hom (pair ⊗ₜ[ℤ] e01) ≠ 0 := by
  intro hz
  have h := congrArg (fun x : (⋀[ℤ]^1 Mat) ⊗[ℤ] Mat =>
    readOne (((⋀[ℤ]^1 Mat).subtype.rTensor Mat) x)) hz
  have h0 : readOne (((⋀[ℤ]^1 Mat).subtype.rTensor Mat)
      (0 : (⋀[ℤ]^1 Mat) ⊗[ℤ] Mat)) = 0 := by
    rw [LinearMap.map_zero, LinearMap.map_zero]
  exact (by decide : (-1 : ℤ) ≠ 0) (secondValue.symm.trans (h.trans h0))
example : K.d 2 1 ≫ K.d 1 0 = 0 := K.d_comp_d 2 1 0
example : (K.d 1 0).hom ((K.d 2 1).hom (pair ⊗ₜ[ℤ] e01)) = 0 := by
  have h := congrArg (fun f => f.hom (pair ⊗ₜ[ℤ] e01)) (K.d_comp_d 2 1 0)
  exact h

end MathlibExtTest.CanonicalCoefficient
