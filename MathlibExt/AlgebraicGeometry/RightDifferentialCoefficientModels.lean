/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RightCoordinateDifferentials
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Coefficient sheaves of actual right differential modules

The coefficient map sends k to the original global constant
multiplication operators, then through native opposite sheafification.
The coefficient sheaf is native module forgetting at the initial open
followed by scalar restriction along that exact ring map. Its sections
and maps retain the original right module. A natural operator realization
is characterized on every original section by the original right action;
it supplies the coefficient-linear maps used by actual Koszul/de Rham
constructions, without selecting a realization functor independently.

Source: Saito1307.2140v5, Sections1.3--1.5; D'Agnolo--Kashiwara
1311.2374v2, Section9.1. Native module forgetting and scalar restriction:
Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679, Apache2.0,
Joël Riou and the Mathlib contributors.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RightDifferentialCoefficientModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite TopologicalSpace
open DifferentialOperatorSheaves RightDifferentialModules RightCoordinateDifferentials

variable (k : Type) [CommRing k] (M : Type) [TopologicalSpace M]
  (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)
  [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]

/-- The full open is the actual initial object in the opposite open category. -/
def fullOpenInitial : IsInitial (op (⊤ : Opens M)) :=
  IsInitial.ofUniqueHom (fun U ↦ (homOfLE (show U.unop ≤ ⊤ from le_top)).op)
    (fun _ _ ↦ Subsingleton.elim _ _)

/-- The coefficient inclusion is literal multiplication by the global constant function. -/
def rightConstantScalar : k →+* (rightDifferentialRing k M O).obj.obj (op ⊤) :=
  (((toSheafify (Opens.grothendieckTopology M) (rightOperatorPresheaf k M O)).app (op ⊤)).hom.comp
    (rightScalarFinite k M O ⊤)).comp (algebraMap k (O.obj (op ⊤)))

/-- The actual coefficient sheaf of a right D-module. -/
def rightCoefficients : RightModule k M O ⥤ TopCat.Sheaf (ModuleCat.{0} k) (TopCat.of M) :=
  SheafOfModules.forgetToSheafModuleCat (rightDifferentialRing k M O)
    (op ⊤) (fullOpenInitial M) ⋙
    sheafCompose (Opens.grothendieckTopology M) (ModuleCat.restrictScalars (rightConstantScalar k M O))

/-- Coefficient forgetting preserves the original local additive sections. -/
def coefficientSection (N : RightModule k M O) (U : Opens M) :
    ((rightCoefficients k M O).obj N).presheaf.obj (op U) ≃+ N.val.obj (op U) :=
  AddEquiv.refl _

/-- The coefficient map of every right D-module morphism is its original local section map. -/
theorem coefficientMap_apply {N N' : RightModule k M O} (f : N ⟶ N') (U : Opens M)
    (s : ((rightCoefficients k M O).obj N).presheaf.obj (op U)) :
    coefficientSection k M O N' U
        (((((rightCoefficients k M O).map f).hom).app (op U)).hom s) =
      ((f.val.app (op U)).hom) (coefficientSection k M O N U s) := rfl

/-- An actual finite-order local operator family, with the original restriction law. -/
structure NaturalOperator where
  operator : ∀ U : Opens M, finiteOperatorRing k M O U
  restriction : ∀ (U V : Opens M) (h : V ≤ U),
    restrictFinite k M O h (operator U) = operator V

/-- The original coordinate derivation gives the same finite partial operator on all opens. -/
def partialOperator (C : CoordinateDerivation k M O) : NaturalOperator k M O where
  operator := partialFinite k M O C
  restriction := by
    intro U V h
    apply Subtype.ext
    apply Subtype.ext
    funext W
    apply LinearMap.ext
    intro x
    rfl

/-- The coefficient-linear realization of an actual natural operator, normalized on all original sections. -/
structure CoefficientOperator (P : NaturalOperator k M O) (N : RightModule k M O) where
  map : End ((rightCoefficients k M O).obj N)
  normalization : ∀ (U : Opens M) (s : N.val.obj (op U)),
    coefficientSection k M O N U
        (((map.asHom.hom.app (op U)).hom) ((coefficientSection k M O N U).symm s)) =
      rightAct k M O N U (P.operator U) s

/-- The source actual coordinate derivative as a coefficient-sheaf endomorphism. -/
def coefficientPartial (C : CoordinateDerivation k M O) (N : RightModule k M O)
    (P : CoefficientOperator k M O (partialOperator k M O C) N) :
    End ((rightCoefficients k M O).obj N) := P.map

end MathlibExt.AlgebraicGeometry.RightDifferentialCoefficientModels
