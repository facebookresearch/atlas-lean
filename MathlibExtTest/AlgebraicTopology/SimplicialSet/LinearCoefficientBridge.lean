/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ChangeOfCategory

open CategoryTheory CategoryTheory.Limits

universe w v₁ v₂ u₁ u₂

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.LinearCoefficientBridge

noncomputable def mapChainComplexFunctorIso_client
    {C : Type u₁} [Category.{v₁} C] [HasCoproducts.{w} C] [Preadditive C]
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{w} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] [PreservesColimitsOfSize.{w, w} F] (R : C) :
    (SSet.chainComplexFunctor C).obj R ⋙
      F.mapHomologicalComplex (ComplexShape.down ℕ) ≅
      (SSet.chainComplexFunctor D).obj (F.obj R) :=
  SSet.mapChainComplexFunctorIso F R

theorem mapChainComplexFunctorIso_hom_naturality_client
    {C : Type u₁} [Category.{v₁} C] [HasCoproducts.{w} C] [Preadditive C]
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{w} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] [PreservesColimitsOfSize.{w, w} F] (R : C)
    {X Y : SSet.{w}} (f : X ⟶ Y) :
    ((SSet.chainComplexFunctor C).obj R ⋙
      F.mapHomologicalComplex (ComplexShape.down ℕ)).map f ≫
      (SSet.mapChainComplexFunctorIso F R).hom.app Y =
      (SSet.mapChainComplexFunctorIso F R).hom.app X ≫
        ((SSet.chainComplexFunctor D).obj (F.obj R)).map f :=
  (SSet.mapChainComplexFunctorIso F R).hom.naturality f

noncomputable def mapRelativeChainComplexFunctorIso_client
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasCoproducts.{w} C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasCoproducts.{w} D]
    (F : C ⥤ D) [F.Additive] [PreservesColimitsOfSize.{w, w} F]
    [PreservesColimitsOfShape WalkingParallelPair
      (F.mapHomologicalComplex (ComplexShape.down ℕ))] (R : C) :
    (SSetPair.relativeChainComplexFunctor (C := C)).obj R ⋙
      F.mapHomologicalComplex (ComplexShape.down ℕ) ≅
      (SSetPair.relativeChainComplexFunctor (C := D)).obj (F.obj R) :=
  SSetPair.mapRelativeChainComplexFunctorIso F R

theorem mapRelativeChainComplexFunctorIso_hom_naturality_client
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasCoproducts.{w} C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasCoproducts.{w} D]
    (F : C ⥤ D) [F.Additive] [PreservesColimitsOfSize.{w, w} F]
    [PreservesColimitsOfShape WalkingParallelPair
      (F.mapHomologicalComplex (ComplexShape.down ℕ))] (R : C)
    {P Q : SSetPair} (f : P ⟶ Q) :
    ((SSetPair.relativeChainComplexFunctor (C := C)).obj R ⋙
      F.mapHomologicalComplex (ComplexShape.down ℕ)).map f ≫
      (SSetPair.mapRelativeChainComplexFunctorIso F R).hom.app Q =
      (SSetPair.mapRelativeChainComplexFunctorIso F R).hom.app P ≫
        ((SSetPair.relativeChainComplexFunctor (C := D)).obj (F.obj R)).map f :=
  (SSetPair.mapRelativeChainComplexFunctorIso F R).hom.naturality f

end MathlibExtTest.AlgebraicTopology.SimplicialSet.LinearCoefficientBridge
