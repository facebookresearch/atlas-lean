/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExtTest.LinearAlgebra.Determinant.QuotientBaseChange
public import MathlibExt.LinearAlgebra.Charpoly.Quotient
public import Mathlib.Algebra.Field.ULift
public import MathlibExt.LinearAlgebra.Determinant.MapCoeffs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Quotient and scalar-transport characteristic polynomials

Modulo (2), the integral diagonal map (3,5) has polynomial (X-1)². Its
left-multiplication presentation gives the same result. Rational scalar
transport to ULift ℚ is tested with caller-provided algebra and module
instances, and a concrete characteristic polynomial.
-/

@[expose] public section

noncomputable section
open Polynomial
namespace MathlibExtTest.QuotientCharpoly
open MathlibExtTest.QuotientBaseChange

theorem quotient_charpoly :
    (diagonal.quotientBaseChange I).charpoly = (X - C (1 : Base)) ^ 2 := by
  rw [LinearMap.charpoly_quotientBaseChange, diagonal_charpoly]
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have h3 : Ideal.Quotient.mk I (3 : ℤ) = 1 := by simpa using residue_odd 1
  have h5 : Ideal.Quotient.mk I (5 : ℤ) = 1 := by simpa using residue_odd 2
  rw [h3, h5, pow_two]

example :
    (Algebra.lmul Base Quot
      (Ideal.Quotient.mk (I.map (algebraMap ℤ S)) ![(3 : ℤ), 5])).charpoly =
        (X - C (1 : Base)) ^ 2 := by
  have hm : Algebra.lmul ℤ S ![(3 : ℤ), 5] = diagonal := by
    ext x i
    fin_cases i <;>
      simp [Algebra.coe_lmul_eq_mul, diagonal, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two]
  calc
    _ = (Algebra.lmul ℤ S ![(3 : ℤ), 5]).charpoly.map (Ideal.Quotient.mk I) :=
      Algebra.charpoly_lmul_quotient_map _ _
    _ = diagonal.charpoly.map (Ideal.Quotient.mk I) := by rw [hm]
    _ = _ := by rw [← LinearMap.charpoly_quotientBaseChange]; exact quotient_charpoly

abbrev V := Fin 2 → ℚ
abbrev LiftedScalar := ULift.{1} ℚ
def scalarEquiv : ℚ ≃+* LiftedScalar := ULift.ringEquiv.symm

instance liftedAlgebra : Algebra LiftedScalar V :=
  ((algebraMap ℚ V).comp (ULift.ringEquiv.toRingHom)).toAlgebra

theorem lifted_smul (c : LiftedScalar) (x : V) : c • x = c.down • x := by
  simp only [Algebra.smul_def]
  rfl

theorem scalarCompatible (c : ℚ) (x : V) : scalarEquiv c • x = c • x := by
  rw [lifted_smul]
  rfl

def liftedBasis : Module.Basis (Fin 2) LiftedScalar V :=
  (Pi.basisFun ℚ (Fin 2)).mapCoeffs scalarEquiv scalarCompatible

instance liftedFree : Module.Free LiftedScalar V := Module.Free.of_basis liftedBasis
instance liftedFinite : Module.Finite LiftedScalar V := Module.Finite.of_basis liftedBasis

def rationalDiagonal : V →ₗ[ℚ] V := Matrix.toLin' (Matrix.diagonal ![(3 : ℚ), 5])

def liftedDiagonal : V →ₗ[LiftedScalar] V where
  toFun := rationalDiagonal
  map_add' := rationalDiagonal.map_add
  map_smul' c x := by
    change rationalDiagonal (c • x) = c • rationalDiagonal x
    rw [lifted_smul, lifted_smul]
    exact rationalDiagonal.map_smul c.down x

example :
    liftedDiagonal.charpoly =
      (X - C (scalarEquiv 3)) * (X - C (scalarEquiv 5)) := by
  rw [← LinearMap.charpoly_mapCoeffs scalarEquiv scalarCompatible
    rationalDiagonal liftedDiagonal (fun _ => rfl)]
  simp [rationalDiagonal, Matrix.charpoly_diagonal, Fin.prod_univ_two]

example : liftedDiagonal.det = scalarEquiv 15 := by
  rw [← LinearMap.det_mapCoeffs scalarEquiv scalarCompatible (Pi.basisFun ℚ (Fin 2))
    rationalDiagonal liftedDiagonal (fun _ => rfl)]
  norm_num [rationalDiagonal, Fin.prod_univ_two]

-- Left multiplication uses the module carried by the given algebra structure.
instance liftedAlgebraFinite :
    @Module.Finite LiftedScalar V _ _ (Algebra.toModule : Module LiftedScalar V) := by
  let m : Module LiftedScalar V := Algebra.toModule
  let : Module LiftedScalar V := m
  have hcompat : ∀ (c : ℚ) (x : V), scalarEquiv c • x = c • x := by
    intro c x
    simp only [Algebra.smul_def]
    rfl
  exact Module.Finite.of_basis
    ((Pi.basisFun ℚ (Fin 2)).mapCoeffs scalarEquiv hcompat)

example :
    (Algebra.lmul LiftedScalar V ![(3 : ℚ), 5]).charpoly =
      (X - C (scalarEquiv 3)) * (X - C (scalarEquiv 5)) := by
  have hm : Algebra.lmul ℚ V ![(3 : ℚ), 5] = rationalDiagonal := by
    ext x i
    fin_cases i <;>
      simp [Algebra.coe_lmul_eq_mul, rationalDiagonal, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two]
  rw [← Algebra.charpoly_lmul_map_ringEquiv scalarEquiv scalarCompatible, hm]
  simp [rationalDiagonal, Matrix.charpoly_diagonal, Fin.prod_univ_two]

end MathlibExtTest.QuotientCharpoly
