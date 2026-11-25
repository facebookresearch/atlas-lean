/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.ModelCategory.QuillenDerivedAdjunction

set_option autoImplicit false

noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory HomotopicalAlgebra MorphismProperty
open CategoryTheory.Functor

namespace MathlibExtTest.QuillenDerivedAdjunction

section PublicSurface

#check @QuillenDerivedAdjunctionData.{v₁, v₂, u₁, u₂}
#check @QuillenDerivedAdjunctionData.{1, 0, 1, 0}
#check @QuillenDerivedAdjunctionData.{0, 1, 0, 1}
#check @QuillenDerivedAdjunctionData.{0, 0, 0, 0}
#check @quillenDerivedAdjunctionData.{v₁, v₂, u₁, u₂}
#check @quillenDerivedAdjunctionData.{1, 0, 1, 0}
#check @quillenDerivedAdjunctionData.{0, 1, 0, 1}
#check @quillenDerivedAdjunctionData.{0, 0, 0, 0}

end PublicSurface

section GenericClient

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  [CategoryTheory.Adjunction.IsQuillenAdjunction adj]

example :
    (weakEquivalences C).Localization ⥤
      (weakEquivalences D).Localization :=
  (quillenDerivedAdjunctionData adj).leftDerived

example :
    (weakEquivalences D).Localization ⥤
      (weakEquivalences C).Localization :=
  (quillenDerivedAdjunctionData adj).rightDerived

example :
    (weakEquivalences C).Q ⋙
        (quillenDerivedAdjunctionData adj).leftDerived ⟶
      L ⋙ (weakEquivalences D).Q :=
  (quillenDerivedAdjunctionData adj).leftComparison

example :
    R ⋙ (weakEquivalences C).Q ⟶
      (weakEquivalences D).Q ⋙
        (quillenDerivedAdjunctionData adj).rightDerived :=
  (quillenDerivedAdjunctionData adj).rightComparison

example :
    (quillenDerivedAdjunctionData adj).leftDerived.IsLeftDerivedFunctor
      (quillenDerivedAdjunctionData adj).leftComparison
      (weakEquivalences C) :=
  (quillenDerivedAdjunctionData adj).leftIsDerived

example :
    (quillenDerivedAdjunctionData adj).rightDerived.IsRightDerivedFunctor
      (quillenDerivedAdjunctionData adj).rightComparison
      (weakEquivalences D) :=
  (quillenDerivedAdjunctionData adj).rightIsDerived

example :
    Functor.IsLeftDerivedFunctor
      ((quillenDerivedAdjunctionData adj).leftDerived ⋙
        (quillenDerivedAdjunctionData adj).rightDerived)
        ((Functor.associator _ _ _).inv ≫
          whiskerRight
            (quillenDerivedAdjunctionData adj).leftComparison
            (quillenDerivedAdjunctionData adj).rightDerived)
        (weakEquivalences C) :=
  (quillenDerivedAdjunctionData adj).leftCompositeIsDerived

example :
    Functor.IsRightDerivedFunctor
      ((quillenDerivedAdjunctionData adj).rightDerived ⋙
        (quillenDerivedAdjunctionData adj).leftDerived)
        (whiskerRight
            (quillenDerivedAdjunctionData adj).rightComparison
            (quillenDerivedAdjunctionData adj).leftDerived ≫
          (Functor.associator _ _ _).hom)
        (weakEquivalences D) :=
  (quillenDerivedAdjunctionData adj).rightCompositeIsDerived

example :
    (quillenDerivedAdjunctionData adj).leftDerived ⊣
      (quillenDerivedAdjunctionData adj).rightDerived :=
  (quillenDerivedAdjunctionData adj).adjunction

example : True := by
  let data := quillenDerivedAdjunctionData adj
  let _ : data.leftDerived.IsLeftDerivedFunctor
      data.leftComparison (weakEquivalences C) := data.leftIsDerived
  let _ : (L ⋙ (weakEquivalences D).Q).HasLeftDerivedFunctor
      (weakEquivalences C) :=
    Functor.HasLeftDerivedFunctor.mk'
      data.leftDerived data.leftComparison
  have : data.leftDerived =
      (L ⋙ (weakEquivalences D).Q).totalLeftDerived
        (weakEquivalences C).Q (weakEquivalences C) := rfl
  trivial

example : True := by
  let data := quillenDerivedAdjunctionData adj
  let _ : data.rightDerived.IsRightDerivedFunctor
      data.rightComparison (weakEquivalences D) := data.rightIsDerived
  let _ : (R ⋙ (weakEquivalences C).Q).HasRightDerivedFunctor
      (weakEquivalences D) :=
    Functor.HasRightDerivedFunctor.mk'
      data.rightDerived data.rightComparison
  have : data.rightDerived =
      (R ⋙ (weakEquivalences C).Q).totalRightDerived
        (weakEquivalences D).Q (weakEquivalences D) := rfl
  trivial

example : True := by
  let data := quillenDerivedAdjunctionData adj
  let _ : data.leftDerived.IsLeftDerivedFunctor
      data.leftComparison (weakEquivalences C) := data.leftIsDerived
  let _ : (L ⋙ (weakEquivalences D).Q).HasLeftDerivedFunctor
      (weakEquivalences C) :=
    Functor.HasLeftDerivedFunctor.mk'
      data.leftDerived data.leftComparison
  have : data.leftComparison =
      (L ⋙ (weakEquivalences D).Q).totalLeftDerivedCounit
        (weakEquivalences C).Q (weakEquivalences C) := rfl
  trivial

example : True := by
  let data := quillenDerivedAdjunctionData adj
  let _ : data.rightDerived.IsRightDerivedFunctor
      data.rightComparison (weakEquivalences D) := data.rightIsDerived
  let _ : (R ⋙ (weakEquivalences C).Q).HasRightDerivedFunctor
      (weakEquivalences D) :=
    Functor.HasRightDerivedFunctor.mk'
      data.rightDerived data.rightComparison
  have : data.rightComparison =
      (R ⋙ (weakEquivalences C).Q).totalRightDerivedUnit
        (weakEquivalences D).Q (weakEquivalences D) := rfl
  trivial

example : True := by
  let data := quillenDerivedAdjunctionData adj
  let _ : data.leftDerived.IsLeftDerivedFunctor
      data.leftComparison (weakEquivalences C) := data.leftIsDerived
  let _ : data.rightDerived.IsRightDerivedFunctor
      data.rightComparison (weakEquivalences D) := data.rightIsDerived
  let _ : (data.leftDerived ⋙ data.rightDerived).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        whiskerRight data.leftComparison data.rightDerived)
      (weakEquivalences C) := data.leftCompositeIsDerived
  let _ : (data.rightDerived ⋙ data.leftDerived).IsRightDerivedFunctor
      (whiskerRight data.rightComparison data.leftDerived ≫
        (Functor.associator _ _ _).hom)
      (weakEquivalences D) := data.rightCompositeIsDerived
  have : data.adjunction =
      adj.derived (weakEquivalences C) (weakEquivalences D)
        data.leftComparison data.rightComparison := rfl
  trivial

end GenericClient

section OrientationAndFieldFalsifiers

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  [CategoryTheory.Adjunction.IsQuillenAdjunction adj]

example : True := by
  let data := quillenDerivedAdjunctionData adj
  fail_if_success
    exact (data.leftComparison :
      L ⋙ (weakEquivalences D).Q ⟶
        (weakEquivalences C).Q ⋙ data.leftDerived)
  trivial

example : True := by
  let data := quillenDerivedAdjunctionData adj
  fail_if_success
    exact (data.rightComparison :
      (weakEquivalences D).Q ⋙ data.rightDerived ⟶
        R ⋙ (weakEquivalences C).Q)
  trivial

example : True := by
  let data := quillenDerivedAdjunctionData adj
  fail_if_success
    let _ : QuillenDerivedAdjunctionData adj :=
      { leftDerived := data.leftDerived
        rightDerived := data.rightDerived
        leftComparison := data.leftComparison
        rightComparison := data.rightComparison
        leftIsDerived := data.leftIsDerived
        rightIsDerived := data.rightIsDerived
        rightCompositeIsDerived := data.rightCompositeIsDerived
        adjunction := data.adjunction }
  trivial

example : True := by
  let data := quillenDerivedAdjunctionData adj
  fail_if_success
    let _ : QuillenDerivedAdjunctionData adj :=
      { leftDerived := data.leftDerived
        rightDerived := data.rightDerived
        leftComparison := data.leftComparison
        rightComparison := data.rightComparison
        leftIsDerived := data.leftIsDerived
        rightIsDerived := data.rightIsDerived
        leftCompositeIsDerived := data.leftCompositeIsDerived
        adjunction := data.adjunction }
  trivial

end OrientationAndFieldFalsifiers

section UnitCounit

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  [CategoryTheory.Adjunction.IsQuillenAdjunction adj]

example (X : C) :
    let data := quillenDerivedAdjunctionData adj
    data.adjunction.unit.app
          ((weakEquivalences C).Q.obj X) ≫
        data.rightDerived.map (data.leftComparison.app X) =
      (weakEquivalences C).Q.map (adj.unit.app X) ≫
        data.rightComparison.app (L.obj X) := by
  let data := quillenDerivedAdjunctionData adj
  let _ : data.leftDerived.IsLeftDerivedFunctor
      data.leftComparison (weakEquivalences C) := data.leftIsDerived
  let _ : data.rightDerived.IsRightDerivedFunctor
      data.rightComparison (weakEquivalences D) := data.rightIsDerived
  let _ : (data.leftDerived ⋙ data.rightDerived).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        whiskerRight data.leftComparison data.rightDerived)
      (weakEquivalences C) := data.leftCompositeIsDerived
  let _ : (data.rightDerived ⋙ data.leftDerived).IsRightDerivedFunctor
      (whiskerRight data.rightComparison data.leftDerived ≫
        (Functor.associator _ _ _).hom)
      (weakEquivalences D) := data.rightCompositeIsDerived
  change (adj.derived (weakEquivalences C) (weakEquivalences D)
      data.leftComparison data.rightComparison).unit.app
        ((weakEquivalences C).Q.obj X) ≫
      data.rightDerived.map (data.leftComparison.app X) =
    (weakEquivalences C).Q.map (adj.unit.app X) ≫
      data.rightComparison.app (L.obj X)
  exact adj.derivedη_fac_app (weakEquivalences C)
    data.leftComparison data.rightComparison X

example (Y : D) :
    let data := quillenDerivedAdjunctionData adj
    data.leftDerived.map (data.rightComparison.app Y) ≫
        data.adjunction.counit.app
            ((weakEquivalences D).Q.obj Y) =
      data.leftComparison.app (R.obj Y) ≫
        (weakEquivalences D).Q.map (adj.counit.app Y) := by
  let data := quillenDerivedAdjunctionData adj
  let _ : data.leftDerived.IsLeftDerivedFunctor
      data.leftComparison (weakEquivalences C) := data.leftIsDerived
  let _ : data.rightDerived.IsRightDerivedFunctor
      data.rightComparison (weakEquivalences D) := data.rightIsDerived
  let _ : (data.leftDerived ⋙ data.rightDerived).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        whiskerRight data.leftComparison data.rightDerived)
      (weakEquivalences C) := data.leftCompositeIsDerived
  let _ : (data.rightDerived ⋙ data.leftDerived).IsRightDerivedFunctor
      (whiskerRight data.rightComparison data.leftDerived ≫
        (Functor.associator _ _ _).hom)
      (weakEquivalences D) := data.rightCompositeIsDerived
  change data.leftDerived.map (data.rightComparison.app Y) ≫
      (adj.derived (weakEquivalences C) (weakEquivalences D)
        data.leftComparison data.rightComparison).counit.app
          ((weakEquivalences D).Q.obj Y) =
    data.leftComparison.app (R.obj Y) ≫
      (weakEquivalences D).Q.map (adj.counit.app Y)
  exact adj.derivedε_fac_app (weakEquivalences D)
    data.leftComparison data.rightComparison Y

example (X : (weakEquivalences C).Localization) :
    let data := quillenDerivedAdjunctionData adj
    data.leftDerived.map (data.adjunction.unit.app X) ≫
        data.adjunction.counit.app (data.leftDerived.obj X) =
      𝟙 (data.leftDerived.obj X) := by
  exact (quillenDerivedAdjunctionData adj).adjunction.left_triangle_components X

example (Y : (weakEquivalences D).Localization) :
    let data := quillenDerivedAdjunctionData adj
    data.adjunction.unit.app (data.rightDerived.obj Y) ≫
        data.rightDerived.map (data.adjunction.counit.app Y) =
      𝟙 (data.rightDerived.obj Y) := by
  exact (quillenDerivedAdjunctionData adj).adjunction.right_triangle_components Y

end UnitCounit

section IdentityClient

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]

example : QuillenDerivedAdjunctionData (Adjunction.id (C := C)) :=
  quillenDerivedAdjunctionData (Adjunction.id (C := C))

end IdentityClient

section MissingPremise

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

example : True := by
  fail_if_success
    exact quillenDerivedAdjunctionData adj
  trivial

end MissingPremise

section NoEquivalenceOverclaim

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  [CategoryTheory.Adjunction.IsQuillenAdjunction adj]

example : True := by
  fail_if_success
    let _ : CategoryTheory.Adjunction.IsQuillenEquivalence adj :=
      inferInstance
  trivial

end NoEquivalenceOverclaim

section Nonclaims

#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.quillenDerivedEquivalence

#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.derivedSuspensionLoopAdjunction

#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.quillenDerivedCofiberFiberAdjunction

#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.fibrantObjectHoCatDerivedAdjunction

end Nonclaims

#print axioms HomotopicalAlgebra.QuillenDerivedAdjunctionData
#print axioms HomotopicalAlgebra.quillenDerivedAdjunctionData

end MathlibExtTest.QuillenDerivedAdjunction
