/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.Basic

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits SimplicialSpace

universe u v w

namespace SimplicialSpaceTest

/-- Wrapping retains the actual bidegree action of an arbitrary map. -/
theorem map_bidegree {X Y : SimplicialObject SSet.{u}} (f : X ⟶ Y)
    (m n : SimplexCategoryᵒᵖ) (x : (X.obj m).obj n) :
    ((forget.map (ofSimplicialObject.map f)).app m).app n x =
      (f.app m).app n x := rfl

/-- A whole Arrow map returns with both original natural transformations. -/
theorem arrow_map_roundtrip
    {f g : Arrow (SimplicialObject SSet.{u})} (sq : f ⟶ g) :
    (forget.mapArrow.map (ofSimplicialObject.mapArrow.map sq)).left = sq.left ∧
      (forget.mapArrow.map (ofSimplicialObject.mapArrow.map sq)).right = sq.right :=
  ⟨rfl, rfl⟩

/-- The original full commuting-square equation survives the Arrow round trip. -/
theorem arrow_square_roundtrip
    {f g : Arrow (SimplicialObject SSet.{u})} (sq : f ⟶ g) :
    (forget.mapArrow.map (ofSimplicialObject.mapArrow.map sq)).left ≫ g.hom =
      f.hom ≫ (forget.mapArrow.map (ofSimplicialObject.mapArrow.map sq)).right := by
  change sq.left ≫ g.hom = f.hom ≫ sq.right
  exact sq.w

/-- The designated Arrow unit retains both identity underlying components. -/
theorem designated_arrow_unit (f : Arrow SimplicialSpace.{u}) :
    (((Functor.mapArrowEquivalence equivalenceSimplicialObject).unitIso.app f).hom.left).hom =
        𝟙 f.left.diagram ∧
      (((Functor.mapArrowEquivalence equivalenceSimplicialObject).unitIso.app f).hom.right).hom =
        𝟙 f.right.diagram :=
  arrow_unit_components f

/-- Native monicity inference works through the designation in both directions. -/
theorem mono_dictionary {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    Mono f ↔ Mono (forget.map f) :=
  (mono_forget_map_iff f).symm

example {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) [Mono f] : Mono (forget.map f) :=
  inferInstance

example {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) [Mono (forget.map f)] : Mono f :=
  forget.mono_of_mono_map inferInstance

/-- The existing native equivalence supplies arbitrary available shape limits. -/
example (J : Type v) [Category.{w} J]
    [HasLimitsOfShape J (SimplicialObject SSet.{u})] :
    HasLimitsOfShape J SimplicialSpace.{u} := inferInstance

end SimplicialSpaceTest
