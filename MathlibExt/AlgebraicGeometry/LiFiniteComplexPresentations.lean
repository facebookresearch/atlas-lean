/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LiCechObstructionComplexes
public import MathlibExt.AlgebraicGeometry.AffineObstructionComplexes
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Pi

/-!
# Native finite-free presentations of Li's actual complexes

Source matrices occur in degrees0/1, and the finite obstruction
replacement occurs in degrees1/2. Replacement compares the full actual
integer-indexed Cech complex in the derived quotient. Coefficients use
the literal tensor differential. The [-1,0] cotangent presentation is
the actual transposed matrix, with the finite basis pairings displayed.
Source: Jun Li arXiv:math/0110113v1, Lemmas1.15/1.21 and Theorems1.20/1.22.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.LiFiniteComplexPresentations

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct BigOperators
attribute [local instance] HasDerivedCategory.standard

variable (A : Type) [CommRing A]

structure Matrix where
  leftRank : ℕ
  rightRank : ℕ
  differential : (Fin leftRank → A) →ₗ[A] (Fin rightRank → A)

variable {A} (F : Matrix A)

abbrev left := Fin F.leftRank → A
abbrev right := Fin F.rightRank → A

variable (I : Type) [AddCommGroup I] [Module A I]

def leftCoefficient : ModuleCat.{0} A := ModuleCat.of A (left F ⊗[A] I)
def rightCoefficient : ModuleCat.{0} A := ModuleCat.of A (right F ⊗[A] I)

def tensorDifferential : leftCoefficient F I ⟶ rightCoefficient F I :=
  ModuleCat.ofHom (TensorProduct.map F.differential LinearMap.id)

def complexAt (degree : ℤ) : CochainComplex (ModuleCat.{0} A) ℤ :=
  CochainComplex.mappingCone
    ((CochainComplex.singleFunctor (ModuleCat.{0} A) degree).map (tensorDifferential F I))

def leftCoefficientMap {N : Type} [AddCommGroup N] [Module A N] (u : I →ₗ[A] N) :
    leftCoefficient F I ⟶ leftCoefficient F N :=
  ModuleCat.ofHom (TensorProduct.map LinearMap.id u)

def rightCoefficientMap {N : Type} [AddCommGroup N] [Module A N] (u : I →ₗ[A] N) :
    rightCoefficient F I ⟶ rightCoefficient F N :=
  ModuleCat.ofHom (TensorProduct.map LinearMap.id u)

def transpose : right F →ₗ[A] left F where
  toFun x i := ∑ j : Fin F.rightRank, F.differential (Pi.single i 1) j * x j
  map_add' x y := by ext i; simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

def dualPresentation : AffineObstructionComplexes.FreeTwoTerm A where
  negativeRank := F.rightRank
  zeroRank := F.leftRank
  differential := transpose F

structure Replacement (L : LiCechObstructionComplexes.Data A) where
  matrix : Matrix A
  comparison : DerivedCategory.Q.obj (LiCechObstructionComplexes.integerComplex L) ≅
    DerivedCategory.Q.obj (complexAt matrix A 2)

/-- Source terms and differential coincide with the actual tensor matrix;
the log cochains remain the specified geometric Cech object. -/
structure SourceBinding (L : LiCechObstructionComplexes.Data A) where
  zero : L.zero ≅ leftCoefficient F I
  one : L.one ≅ rightCoefficient F I
  differential : L.sourceDifferential ≫ one.hom = zero.hom ≫ tensorDifferential F I

end MathlibExt.AlgebraicGeometry.LiFiniteComplexPresentations
