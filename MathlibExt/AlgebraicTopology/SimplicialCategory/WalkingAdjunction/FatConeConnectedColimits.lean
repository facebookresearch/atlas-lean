/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.FatConeAdjunction
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Actual connected-colimit and pushout preservation of both cone functors

The genuine structured fat-cone and original join-cone adjunctions
preserve colimits under their fixed point. Forgetting the point
preserves connected colimits. Consequently both original whole cone
functors preserve connected colimits and actual pushout squares.
The original comparison is the identical projected natural
transformation. No preservation of empty colimits or arbitrary
coproducts after forgetting the point is asserted.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped Simplicial

namespace SSet.WalkingAdjunction.FatCone

/-- The actual whole fat-cone functor obtained by forgetting its fixed original point. -/
abbrev underlyingFunctor : SSet.{u} ⥤ SSet.{u} := underFunctor ⋙ Under.forget (Δ[0] : SSet.{u})

/-- The existing whole original join-cone functor obtained by forgetting its fixed point. -/
abbrev joinFunctor : SSet.{u} ⥤ SSet.{u} := joinOver (Δ[0] : SSet.{u}) ⋙ Under.forget (Δ[0] : SSet.{u})

/-- The actual whole fat-cone functor preserves connected colimits at independent shape universes. -/
theorem underlying_preservesColimitsOfShape (J : Type v) [Category.{w} J] [IsConnected J] :
    PreservesColimitsOfShape J underlyingFunctor.{u} := by
  let _ : PreservesColimitsOfShape J underFunctor.{u} := preservesColimitsOfShape J
  infer_instance

/-- The existing whole join-cone functor preserves connected colimits through its actual adjunction. -/
theorem join_preservesColimitsOfShape (J : Type v) [Category.{w} J] [IsConnected J] :
    PreservesColimitsOfShape J joinFunctor.{u} := by
  let _ : PreservesColimitsOfShape J (joinOver (Δ[0] : SSet.{u})) :=
    (joinOverAdjunction (Δ[0] : SSet.{u})).leftAdjoint_preservesColimits.preservesColimitsOfShape
  infer_instance

/-- The entire original fat-cone maps send each original pushout square to its actual pushout square. -/
theorem map_isPushout {A B C D : SSet.{u}} {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (h : IsPushout f g i j) : IsPushout (map f) (map g) (map i) (map j) := by
  let _ : PreservesColimitsOfShape WalkingSpan underlyingFunctor.{u} :=
    underlying_preservesColimitsOfShape WalkingSpan
  exact h.map underlyingFunctor

/-- The existing entire join maps send each original pushout square to its identical original pushout square. -/
theorem join_map_isPushout {A B C D : SSet.{u}} {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (h : IsPushout f g i j) :
    IsPushout ((join.map f).app Δ[0]) ((join.map g).app Δ[0])
      ((join.map i).app Δ[0]) ((join.map j).app Δ[0]) := by
  let _ : PreservesColimitsOfShape WalkingSpan joinFunctor.{u} := join_preservesColimitsOfShape WalkingSpan
  exact h.map joinFunctor

/-- The actual fat cone sends any supplied genuine connected colimit cocone to its genuine colimit cocone. -/
def mapIsColimit {J : Type v} [Category.{w} J] [IsConnected J]
    {F : J ⥤ SSet.{u}} {c : Cocone F} (h : IsColimit c) : IsColimit (underlyingFunctor.mapCocone c) := by
  let _ : PreservesColimitsOfShape J underlyingFunctor.{u} := underlying_preservesColimitsOfShape J
  exact isColimitOfPreserves underlyingFunctor h

/-- The original join cone sends any supplied genuine connected colimit cocone to its genuine colimit cocone. -/
def joinMapIsColimit {J : Type v} [Category.{w} J] [IsConnected J]
    {F : J ⥤ SSet.{u}} {c : Cocone F} (h : IsColimit c) : IsColimit (joinFunctor.mapCocone c) := by
  let _ : PreservesColimitsOfShape J joinFunctor.{u} := join_preservesColimitsOfShape J
  exact isColimitOfPreserves joinFunctor h

/-- The actual original whole cone comparison as the projected native natural transformation. -/
def underlyingComparison : underlyingFunctor.{u} ⟶ joinFunctor :=
  Functor.whiskerRight joinComparison (Under.forget (Δ[0] : SSet.{u}))

/-- Projection of the native comparison retains the identical original full comparison map. -/
theorem underlyingComparison_app (X : SSet.{u}) : underlyingComparison.app X = toJoin X := rfl

end SSet.WalkingAdjunction.FatCone
