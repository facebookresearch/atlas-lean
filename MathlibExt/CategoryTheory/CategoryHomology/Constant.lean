/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryHomology.Initial
public import MathlibExt.CategoryTheory.NerveData
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence

/-!
# Constant coefficient category bar

For constant coefficients `R`, the coefficient category bar is the
degreewise coproduct linearization of the nerve.  This file records the
definitional equality at the simplicial-data level and the resulting
isomorphism of genuine simplicial objects.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CategoryHomology

variable (C : Type u₁) [Category.{v₁} C]
  (A : Type u₂) [Category.{v₂} A]
  [HasCoproducts.{max u₁ v₁} A]

/-- Degreewise coproduct linearization of the nerve data. -/
noncomputable def linearizedNerveData (R : A) : SimplicialObject.Data A :=
  SimplicialObject.Data.mapObj
    ((sigmaConst : A ⥤ (Type (max u₁ v₁) ⥤ A)).obj R)
    (nerveData C)

/-- For constant coefficients, the coefficient bar data is definitionally
the linearized nerve data. -/
theorem coefficientBarData_const_eq_linearizedNerveData (R : A) :
    coefficientBarData ((Functor.const C).obj R) =
      linearizedNerveData C A R := rfl

/-- The constant coefficient bar simplicial object identifies with the nerve
linearized degreewise by coproducts of copies of `R`. -/
noncomputable def constantCoefficientBarSimplicialIso (R : A) :
    coefficientBarSimplicial ((Functor.const C).obj R) ≅
      (nerve C ⋙
        ((sigmaConst : A ⥤ (Type (max u₁ v₁) ⥤ A)).obj R)) :=
  (SimplicialObject.Data.toSimplicialObject_mapObjIso
      ((sigmaConst : A ⥤ (Type (max u₁ v₁) ⥤ A)).obj R)
      (nerveData C)).symm ≪≫
    Functor.isoWhiskerRight (nerveDataSimplicialIso C)
      ((sigmaConst : A ⥤ (Type (max u₁ v₁) ⥤ A)).obj R)

section

variable [Preadditive A]

/-- The unnormalized constant coefficient bar complex is the ordinary
simplicial chain complex of the nerve. -/
noncomputable def constantCoefficientBarComplexIso (R : A) :
    coefficientBarComplex ((Functor.const C).obj R) ≅
      (nerve C).chainComplex R :=
  (AlgebraicTopology.alternatingFaceMapComplex A).mapIso
    (constantCoefficientBarSimplicialIso C A R)

end

section

variable [Abelian A]

/-- Category homology with a constant coefficient system agrees with
ordinary simplicial homology of the nerve. -/
noncomputable def homologyWithConstantCoefficientsIso (R : A) (n : ℕ) :
    homologyWithCoefficients ((Functor.const C).obj R) n ≅
      (nerve C).homology R n :=
  (AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
      (Y := coefficientBarSimplicial ((Functor.const C).obj R))).toHomologyIso n ≪≫
    HomologicalComplex.homologyMapIso
      (constantCoefficientBarComplexIso C A R) n

end

end CategoryTheory.CategoryHomology

end
