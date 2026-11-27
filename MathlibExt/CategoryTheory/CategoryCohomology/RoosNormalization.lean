/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.CosimplicialObject.Normalization
public import MathlibExt.CategoryTheory.CategoryCohomology.RoosComplex

/-!
# Normalized Roos cochains

In an abelian coefficient category with sized products, the full Roos
cosimplicial object has a normalized cochain complex. Projection and inclusion
are natural quasi-isomorphisms, and the inclusion induces the cohomology
comparison. The normalized object agrees with the opposite of the normalized
coefficient bar construction.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicTopology
open CategoryTheory.CategoryHomology

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CategoryCohomology

variable {I : Type u₁} [Category.{v₁} I]
  {A : Type u₂} [Category.{v₂} A] [Abelian A] [HasProducts.{max u₁ v₁} A]

/-- The normalized cochain functor of the full weak-chain Roos object. -/
abbrev normalizedRoosComplexFunctor : (I ⥤ A) ⥤ CochainComplex A ℕ :=
  roosCosimplicialFunctor ⋙ normalizedCofaceMapComplex A

/-- The full Roos complex projects naturally to its normalization. -/
abbrev roosNormalizationProjection :
    roosComplexFunctor (I := I) (A := A) ⟶
      normalizedRoosComplexFunctor (I := I) (A := A) :=
  Functor.whiskerLeft (roosCosimplicialFunctor (I := I) (A := A))
    (normalizedCofaceMapProjection A)

/-- The normalized object includes naturally in the full Roos complex. -/
abbrev inclusionOfNormalizedRoosComplex :
    normalizedRoosComplexFunctor (I := I) (A := A) ⟶
      roosComplexFunctor (I := I) (A := A) :=
  Functor.whiskerLeft (roosCosimplicialFunctor (I := I) (A := A))
    (inclusionOfNormalizedCofaceMapComplex A)

/-- The normalized Roos object is the dual of the existing normalized coefficient bar. -/
def normalizedRoosComplexObjIso (M : I ⥤ A) :
    (normalizedRoosComplexFunctor (I := I) (A := A)).obj M ≅
      (chainComplexUnopFunctor A).obj (op (normalizedCoefficientBarComplex M.op)) := by
  let S := coefficientBarSimplicial M.op
  have e : (cosimplicialSimplicialEquiv A).functor.obj (op (roosCosimplicial M)) ≅ S := by
    change S.unop.op ≅ S
    exact Functor.unopOpIso S
  exact (chainComplexUnopFunctor A).mapIso
    (((normalizedMooreComplex Aᵒᵖ).mapIso e).symm.op)

/-- The Roos normalization projection is a quasi-isomorphism. -/
instance roosNormalizationProjection_app_quasiIso (M : I ⥤ A) :
    QuasiIso ((roosNormalizationProjection (I := I) (A := A)).app M) := by
  change QuasiIso ((normalizedCofaceMapProjection A).app (roosCosimplicial M))
  infer_instance

/-- The normalized Roos inclusion is a quasi-isomorphism. -/
instance inclusionOfNormalizedRoosComplex_app_quasiIso (M : I ⥤ A) :
    QuasiIso ((inclusionOfNormalizedRoosComplex (I := I) (A := A)).app M) := by
  change QuasiIso ((inclusionOfNormalizedCofaceMapComplex A).app (roosCosimplicial M))
  infer_instance

/-- Normalized and full Roos cohomology are naturally identified by the inclusion. -/
def normalizedRoosHomologyIso (n : ℕ) :
    (normalizedRoosComplexFunctor (I := I) (A := A) ⋙
        HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) n) ≅
      (roosComplexFunctor (I := I) (A := A) ⋙
        HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) n) :=
  Functor.associator (roosCosimplicialFunctor (I := I) (A := A))
      (normalizedCofaceMapComplex A)
      (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) n) ≪≫
    Functor.isoWhiskerLeft (roosCosimplicialFunctor (I := I) (A := A))
      (normalizedCofaceHomologyIso A n) ≪≫
      (Functor.associator (roosCosimplicialFunctor (I := I) (A := A))
        (alternatingCofaceMapComplex A)
        (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) n)).symm

end CategoryTheory.CategoryCohomology

end
