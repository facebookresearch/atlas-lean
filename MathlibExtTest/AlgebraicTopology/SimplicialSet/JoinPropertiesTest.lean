/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinProperties

/-!
# Tests for basic properties of the join of simplicial sets

Consumer checks for `SSet.Join` properties: Day tensoring and the join
preserve connected colimits (coequalizers, pushouts, filtered colimits),
the canonical inclusions and their naturality, associativity, and the
failure of the join to preserve initial objects.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory Limits
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.JoinPropertiesTest

/-- Day tensoring preserves coequalizers and pushouts in `DayCat`. -/
example (F : SSet.Join.DayCat.{u}) :
    PreservesColimitsOfShape WalkingParallelPair (tensorLeft F) :=
  inferInstance

example (F : SSet.Join.DayCat.{u}) :
    PreservesColimitsOfShape WalkingSpan (tensorRight F) :=
  inferInstance

/-- The join preserves coequalizers in the right variable. -/
example (X : SSet.{u}) :
    PreservesColimitsOfShape WalkingParallelPair (SSet.join.obj X) :=
  inferInstance

/-- The join preserves pushouts in the left variable. -/
example (Y : SSet.{u}) :
    PreservesColimitsOfShape WalkingSpan (SSet.join.flip.obj Y) :=
  inferInstance

/-- A concrete coequalizer is preserved by joining on the left. -/
example {A B Z : SSet.{u}} (f g : A ⟶ B) :
    PreservesColimit (parallelPair f g) (SSet.join.obj Z) :=
  inferInstance

/-- The join preserves filtered colimits in both variables. -/
example {J : Type u} [SmallCategory J] [IsFiltered J] (X : SSet.{u}) :
    PreservesColimitsOfShape J (SSet.join.obj X) :=
  SSet.preservesColimitsOfShape_join_obj_of_isFiltered X

example {J : Type u} [SmallCategory J] [IsFiltered J] (Y : SSet.{u}) :
    PreservesColimitsOfShape J (SSet.join.flip.obj Y) :=
  SSet.preservesColimitsOfShape_join_flip_obj_of_isFiltered Y

/-- The canonical inclusions into a join. -/
example (X Y : SSet.{u}) : X ⟶ X ⋆ Y := SSet.joinInl X Y

example (X Y : SSet.{u}) : Y ⟶ X ⋆ Y := SSet.joinInr X Y

/-- At the empty simplicial set, the inclusions are the unit isomorphisms. -/
example (X : SSet.{u}) : SSet.joinInl X (⊥_ SSet.{u}) = (SSet.joinBotIso X).inv := by
  simp

example (Y : SSet.{u}) : SSet.joinInr (⊥_ SSet.{u}) Y = (SSet.botJoinIso Y).inv := by
  simp

/-- Naturality of the inclusions. -/
example {Y Y' : SSet.{u}} (X : SSet.{u}) (g : Y ⟶ Y') :
    SSet.joinInl X Y ≫ (SSet.join.obj X).map g = SSet.joinInl X Y' :=
  SSet.joinInl_comp_map X g

example {X X' : SSet.{u}} (f : X ⟶ X') (Y : SSet.{u}) :
    f ≫ SSet.joinInl X' Y = SSet.joinInl X Y ≫ (SSet.join.map f).app Y :=
  SSet.map_comp_joinInl f Y

example {X X' : SSet.{u}} (f : X ⟶ X') (Y : SSet.{u}) :
    SSet.joinInr X Y ≫ (SSet.join.map f).app Y = SSet.joinInr X' Y :=
  SSet.joinInr_comp_map f Y

example {Y Y' : SSet.{u}} (g : Y ⟶ Y') (X : SSet.{u}) :
    g ≫ SSet.joinInr X Y' = SSet.joinInr X Y ≫ (SSet.join.obj X).map g :=
  SSet.map_comp_joinInr g X

/-- Associativity of the join. -/
example (X Y Z : SSet.{u}) : (X ⋆ Y) ⋆ Z ≅ X ⋆ (Y ⋆ Z) :=
  SSet.joinAssocIso X Y Z

/-- On standard simplices both associations of `Δ[0] ⋆ Δ[0] ⋆ Δ[0]` give
`Δ[2]`. -/
example : ((Δ[0] ⋆ Δ[0]) ⋆ Δ[0] : SSet.{u}) ≅ Δ[2] :=
  SSet.joinAssocIso Δ[0] Δ[0] Δ[0] ≪≫
    (SSet.join.obj Δ[0]).mapIso (SSet.joinStdSimplexIso 0 0) ≪≫
      SSet.joinStdSimplexIso 0 1

/-- Augmentation of a join is the Day tensor of the augmentations. -/
example (X Y : SSet.{u}) :
    SSet.Join.augDay.obj (X ⋆ Y) ≅ SSet.Join.augDay.obj X ⊗ SSet.Join.augDay.obj Y :=
  SSet.Join.augDayJoinIso X Y

/-- Augmentation preserves monomorphisms. -/
example {X Y : SSet.{u}} {f : X ⟶ Y} [Mono f] : Mono (SSet.Join.aug.map f) :=
  SSet.Join.aug_map_mono

/-- The join does not preserve initial objects: `Δ[0] ⋆ ⊥` is not initial. -/
example (h : IsInitial (Δ[0] ⋆ (⊥_ SSet.{u}))) : False :=
  SSet.not_isInitial_joinBot_one h

end MathlibExtTest.AlgebraicTopology.SimplicialSet.JoinPropertiesTest
