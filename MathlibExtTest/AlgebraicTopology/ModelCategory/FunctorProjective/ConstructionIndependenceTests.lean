/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.ConstructionIndependence

set_option autoImplicit false
noncomputable section

universe w w' uD vD uC vC

open CategoryTheory CategoryTheory.MorphismProperty
open HomotopicalAlgebra HomotopicalAlgebra.FunctorProjective

namespace ProjectiveConstructionIndependencePublicClients

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] {kappa : Cardinal.{w}} [Fact kappa.IsRegular]
  [OrderBot kappa.ord.ToType] (d : CofibrantGenerationData C kappa)
  (s : Functor.EssentialIndexData.{w} D C)
  {kappa' : Cardinal.{w'}} [Fact kappa'.IsRegular] [OrderBot kappa'.ord.ToType]
  (d' : CofibrantGenerationData C kappa') (s' : Functor.EssentialIndexData.{w'} D C)

/-- The whole model records agree for independent working universes and
actual coefficient and small-index witnesses. -/
example : SourceConstruction.FromData.modelCategory d s =
    SourceConstruction.FromData.modelCategory d' s' :=
  SourceConstruction.FromData.modelCategory_eq d s d' s'

/-- Both first-factor comparisons are actual weak maps satisfying all four
original triangles; no equality of their native middle objects is required. -/
theorem bothFirstTriangles (f : Arrow (D ⥤ C)) :
    ∃ (forward : (SourceConstruction.FromData.cofibrantFactorizationData d s).Z.obj f ⟶
        (SourceConstruction.FromData.cofibrantFactorizationData d' s').Z.obj f)
      (backward : (SourceConstruction.FromData.cofibrantFactorizationData d' s').Z.obj f ⟶
        (SourceConstruction.FromData.cofibrantFactorizationData d s).Z.obj f),
      (SourceConstruction.FromData.cofibrantFactorizationData d s).i.app f ≫ forward =
          (SourceConstruction.FromData.cofibrantFactorizationData d' s').i.app f ∧
        forward ≫ (SourceConstruction.FromData.cofibrantFactorizationData d' s').p.app f =
          (SourceConstruction.FromData.cofibrantFactorizationData d s).p.app f ∧
        (SourceConstruction.FromData.cofibrantFactorizationData d' s').i.app f ≫ backward =
          (SourceConstruction.FromData.cofibrantFactorizationData d s).i.app f ∧
        backward ≫ (SourceConstruction.FromData.cofibrantFactorizationData d s).p.app f =
          (SourceConstruction.FromData.cofibrantFactorizationData d' s').p.app f ∧
        (weakEquivalences C).functorCategory D forward ∧
        (weakEquivalences C).functorCategory D backward := by
  exact ⟨SourceConstruction.FromData.cofibrantComparison d s d' s' f,
    SourceConstruction.FromData.cofibrantComparison d' s' d s f,
    (SourceConstruction.FromData.cofibrantComparison_triangles d s d' s' f).1,
    (SourceConstruction.FromData.cofibrantComparison_triangles d s d' s' f).2,
    (SourceConstruction.FromData.cofibrantComparison_triangles d' s' d s f).1,
    (SourceConstruction.FromData.cofibrantComparison_triangles d' s' d s f).2,
    SourceConstruction.FromData.cofibrantComparison_weak d s d' s' f,
    SourceConstruction.FromData.cofibrantComparison_weak d' s' d s f⟩

/-- Original index actions belong to the same whole first and second
comparison transformations, rather than unrelated componentwise lifts. -/
theorem comparisonOriginalActions (f : Arrow (D ⥤ C)) {a b : D} (h : a ⟶ b) :
    ((SourceConstruction.FromData.cofibrantFactorizationData d s).Z.obj f).map h ≫
        (SourceConstruction.FromData.cofibrantComparison d s d' s' f).app b =
      (SourceConstruction.FromData.cofibrantComparison d s d' s' f).app a ≫
        ((SourceConstruction.FromData.cofibrantFactorizationData d' s').Z.obj f).map h ∧
    ((SourceConstruction.FromData.fibrantFactorizationData d s).Z.obj f).map h ≫
        (SourceConstruction.FromData.fibrantComparison d s d' s' f).app b =
      (SourceConstruction.FromData.fibrantComparison d s d' s' f).app a ≫
        ((SourceConstruction.FromData.fibrantFactorizationData d' s').Z.obj f).map h :=
  ⟨(SourceConstruction.FromData.cofibrantComparison d s d' s' f).naturality h,
    (SourceConstruction.FromData.fibrantComparison d s d' s' f).naturality h⟩

/-- All four associated Arrow maps fix the unchanged original endpoints. -/
theorem fourOriginalEndpoints (f : Arrow (D ⥤ C)) :
    (SourceConstruction.FromData.cofibrantComparisonLeftArrow d s d' s' f).left = 𝟙 f.left ∧
      (SourceConstruction.FromData.cofibrantComparisonRightArrow d s d' s' f).right = 𝟙 f.right ∧
      (SourceConstruction.FromData.fibrantComparisonLeftArrow d s d' s' f).left = 𝟙 f.left ∧
      (SourceConstruction.FromData.fibrantComparisonRightArrow d s d' s' f).right = 𝟙 f.right :=
  ⟨(SourceConstruction.FromData.cofibrantComparisonArrow_endpoints d s d' s' f).1,
    (SourceConstruction.FromData.cofibrantComparisonArrow_endpoints d s d' s' f).2.1,
    (SourceConstruction.FromData.fibrantComparisonArrow_endpoints d s d' s' f).1,
    (SourceConstruction.FromData.fibrantComparisonArrow_endpoints d s d' s' f).2.1⟩

/-- The same second comparison retains the two original component equations
and weak-equivalence membership at every original index object. -/
theorem secondComparisonAtEveryObject (f : Arrow (D ⥤ C)) (a : D) :
    ((SourceConstruction.FromData.fibrantFactorizationData d s).i.app f).app a ≫
        (SourceConstruction.FromData.fibrantComparison d s d' s' f).app a =
      ((SourceConstruction.FromData.fibrantFactorizationData d' s').i.app f).app a ∧
    (SourceConstruction.FromData.fibrantComparison d s d' s' f).app a ≫
        ((SourceConstruction.FromData.fibrantFactorizationData d' s').p.app f).app a =
      ((SourceConstruction.FromData.fibrantFactorizationData d s).p.app f).app a ∧
    weakEquivalences C ((SourceConstruction.FromData.fibrantComparison d s d' s' f).app a) :=
  ⟨NatTrans.congr_app (SourceConstruction.FromData.fibrantComparison_triangles d s d' s' f).1 a,
    NatTrans.congr_app (SourceConstruction.FromData.fibrantComparison_triangles d s d' s' f).2 a,
    SourceConstruction.FromData.fibrantComparison_weak d s d' s' f a⟩

section ConventionalEntry

variable [IsCombinatorialModelCategory.{w} C] [EssentiallySmall.{w} D]

/-- The conventional constructor agrees with arbitrary independent actual
source certificates, including a different working universe. -/
example : SourceConstruction.modelCategory (D := D) (C := C) =
    SourceConstruction.FromData.modelCategory d' s' :=
  SourceConstruction.modelCategory_eq_fromData d' s'

/-- An actual weak map compares the selected native first factor to an
independent source factor, retaining both original endpoint triangles. -/
example (f : Arrow (D ⥤ C)) :
    ∃ h : (SourceConstruction.cofibrantFactorizationData (D := D) (C := C)).Z.obj f ⟶
        (SourceConstruction.FromData.cofibrantFactorizationData d' s').Z.obj f,
      (weakEquivalences C).functorCategory D h ∧
        (SourceConstruction.cofibrantFactorizationData (D := D) (C := C)).i.app f ≫ h =
          (SourceConstruction.FromData.cofibrantFactorizationData d' s').i.app f ∧
        h ≫ (SourceConstruction.FromData.cofibrantFactorizationData d' s').p.app f =
          (SourceConstruction.cofibrantFactorizationData (D := D) (C := C)).p.app f := by
  let : Fact (SourceConstruction.cardinal C).IsRegular :=
    SourceConstruction.cardinal_regular C
  let : OrderBot (SourceConstruction.cardinal C).ord.ToType := SourceConstruction.orderBot C
  let a := SourceConstruction.baseData C
  let t := SourceConstruction.essentialIndex (D := D) (C := C)
  exact ⟨SourceConstruction.FromData.cofibrantComparison a t d' s' f,
    SourceConstruction.FromData.cofibrantComparison_weak a t d' s' f,
    SourceConstruction.FromData.cofibrantComparison_triangles a t d' s' f⟩

end ConventionalEntry

end ProjectiveConstructionIndependencePublicClients
