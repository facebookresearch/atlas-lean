/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Limits.TransfiniteCompletion
import Batteries.Tactic.Lint

public section
noncomputable section
universe w u v
open CategoryTheory Limits MorphismProperty
open CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion

section
variable {C : Type u} [Category.{v} C]
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y} (c : TransfiniteCompositionOfShape O f)

example (a : O) : (diagram c).obj (a : WithTop O) = c.F.obj a := diagram_obj_coe c a
example : (diagram c).obj ⊤ = Y := diagram_obj_top c
example {a b : O} (h : a ≤ b) :
    (diagram c).map (homOfLE (WithTop.coe_le_coe.mpr h)) = c.F.map (homOfLE h) :=
  diagram_map_coe c h
example (a : O) : (diagram c).map (homOfLE (le_top : (a : WithTop O) ≤ ⊤)) = c.incl.app a :=
  diagram_map_top c a
example : (shape c).isoBot = c.isoBot := shape_isoBot c
example (a : O) : (shape c).incl.app (a : WithTop O) = c.incl.app a := shape_incl_coe c a
example : (shape c).incl.app ⊤ = 𝟙 Y := shape_incl_top c
example : (shape c).isoBot.inv ≫ (shape c).incl.app ⊥ = f := (shape c).fac
example : (diagram c).IsWellOrderContinuous := continuous c
example : IsColimit (endpointCocone c) := endpointIsColimit c
example (s : Cocone (diagram c)) : (endpointIsColimit c).desc s = s.ι.app ⊤ := rfl
example (s : Cocone (diagram c)) (a : WithTop O) :
    (endpointCocone c).ι.app a ≫ (endpointIsColimit c).desc s = s.ι.app a :=
  (endpointIsColimit c).fac s a
example (s : Cocone (diagram c)) (m : Y ⟶ s.pt)
    (h : ∀ a, (endpointCocone c).ι.app a ≫ m = s.ι.app a) :
    m = (endpointIsColimit c).desc s := (endpointIsColimit c).uniq s m h
example : IsColimit ((Set.principalSegIio (⊤ : WithTop O)).cocone (diagram c)) := topPrefixIsColimit c
example (a : O) (ha : IsMax a) : IsIso (c.incl.app a) := originalMaxEndpoint_isIso c a ha
end

#print axioms CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion.obj
#print axioms CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion.map
#print axioms CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion.map_id
#print axioms CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion.map_comp
#print axioms CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion.diagram
#print axioms CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion.diagram_obj_coe
#print axioms CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion.diagram_obj_top
#print axioms CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion.diagram_map_coe
#print axioms CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion.diagram_map_top
#print axioms CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion.botIso
#print axioms CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion.endpointCocone
#print axioms CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion.endpointCocone_coe
#print axioms CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion.endpointCocone_top
#print axioms CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion.endpointIsColimit
#print axioms CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion.topPrefixEquiv
#print axioms CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion.coePrefixEquiv
#print axioms CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion.continuous
#print axioms CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion.originalMaxEndpoint_isIso
#print axioms CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion.shape
#print axioms CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion.shape_functor
#print axioms CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion.shape_isoBot
#print axioms CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion.shape_incl_coe
#print axioms CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion.shape_incl_top
#print axioms CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion.topPrefixIsColimit

#lint only unusedArguments in MathlibExt.CategoryTheory.Limits.TransfiniteCompletion
