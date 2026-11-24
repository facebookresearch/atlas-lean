/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.SmallObject.CellularNormalization.Closure

/-!
# Public clients of actual cellular normalization and closure

These clients retain the original functor, maps, root and endpoint at the same
arrow. Independent outer and inner universes, a greatest outer stage, fixed-map
cobase change and the whole coproduct arrow are exercised explicitly.
-/

set_option autoImplicit false
noncomputable section

universe w w' ν u v

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.SmallObject.CellularNormalization

namespace CellularNormalizationClosurePublicUse

section OriginalPresentation

variable {C : Type u} [Category.{v} C]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {X Y : C} {f : X ⟶ Y} (outer : TransfiniteCompositionOfShape J f)
  (K : {j : J // ¬ IsMax j} → OriginalInnerShape.{w'})
  (c : ∀ i, TransfiniteCompositionOfShape (K i).carrier
    (outer.F.map (homOfLE (Order.le_succ i.1))))

local instance (j : J) : LinearOrder (originalCompletedFamily K j) :=
  (completeOriginalShapes K j).linearOrder
local instance (j : J) : OrderBot (originalCompletedFamily K j) :=
  (completeOriginalShapes K j).orderBot
local instance (j : J) : SuccOrder (originalCompletedFamily K j) :=
  (completeOriginalShapes K j).succOrder
local instance (j : J) : WellFoundedLT (originalCompletedFamily K j) :=
  (completeOriginalShapes K j).wellFounded
local instance : WellFoundedLT (Index (originalCompletedFamily K)) := lexWellFounded
local instance : SuccOrder (Index (originalCompletedFamily K)) := flatSuccOrder

example (P : MorphismProperty C)
    (hc : ∀ i k (_ : ¬ IsMax k),
      (P.coproducts.{ν}).pushouts ((c i).F.map (homOfLE (Order.le_succ k))))
    (emptySource : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (emptyTarget : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (hSource : IsColimit emptySource) (hTarget : IsColimit emptyTarget) :
    ∃ d : (P.coproducts.{ν}).pushouts.TransfiniteCompositionOfShape
        (Index (originalCompletedFamily K)) f,
      d.F = diagram outer.F (completeOriginalHistories outer.F K c) ∧
      (∀ (i j : Index (originalCompletedFamily K)) (h : i ≤ j),
        d.F.map (homOfLE h) ≍
          (diagram outer.F (completeOriginalHistories outer.F K c)).map (homOfLE h)) ∧
      d.incl ≍ endpoint outer.F (completeOriginalHistories outer.F K c) outer.incl ∧
      d.isoBot ≍ (completeOriginalHistories outer.F K c ⊥).isoBot ≪≫ outer.isoBot := by
  obtain ⟨d, hF, hEndpoint, hRoot⟩ :=
    originalHistories_presentation outer K c P hc emptySource emptyTarget hSource hTarget
  refine ⟨d, hF, ?_, hEndpoint, hRoot⟩
  intro i j h
  rw [hF]

end OriginalPresentation

section MixedOriginalUniverses

variable {C : Type u} [Category.{v} C] (P : MorphismProperty C)
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {X Y : C} {f : X ⟶ Y}
  (outer : (MorphismProperty.transfiniteCompositions.{w'}
    (P.coproducts.{ν}).pushouts).TransfiniteCompositionOfShape J f)
  (emptySource : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
  (emptyTarget : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
  (hSource : IsColimit emptySource) (hTarget : IsColimit emptyTarget)

example : MorphismProperty.transfiniteCompositions.{max w w'}
    (P.coproducts.{ν}).pushouts f :=
  transfiniteComposition_mem P outer emptySource emptyTarget hSource hTarget

end MixedOriginalUniverses

section ActualGreatestOuterStage

variable {C : Type u} [Category.{v} C] (P : MorphismProperty C)
  {X Y : C} {f : X ⟶ Y}
  (outer : (MorphismProperty.transfiniteCompositions.{w'}
    (P.coproducts.{ν}).pushouts).TransfiniteCompositionOfShape (Fin 2) f)
  (emptySource : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
  (emptyTarget : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
  (hSource : IsColimit emptySource) (hTarget : IsColimit emptyTarget)

example : MorphismProperty.transfiniteCompositions.{w'}
    (P.coproducts.{ν}).pushouts f :=
  transfiniteComposition_mem P outer emptySource emptyTarget hSource hTarget

end ActualGreatestOuterStage

section FixedCobaseChange

variable {C : Type u} [Category.{v} C] (P : MorphismProperty C)
  {A B X Z : C} {f : A ⟶ B} (a : A ⟶ X) [HasPushoutsAlong a]
  {q : X ⟶ Z} {b : B ⟶ Z} (sq : IsPushout a f q b)
  (hf : MorphismProperty.transfiniteCompositions.{w} (P.coproducts.{ν}).pushouts f)

example : MorphismProperty.transfiniteCompositions.{w} (P.coproducts.{ν}).pushouts q :=
  cobaseChange_mem P a sq hf

end FixedCobaseChange

section ActualCoproductArrow

variable {C : Type u} [Category.{v} C] (P : MorphismProperty C) [HasPushouts C]
  {I : Type w} [HasColimitsOfShape (Discrete I) C]
  {A B : I → C} (f : ∀ i, A i ⟶ B i)
  (hf : ∀ i, MorphismProperty.transfiniteCompositions.{w'} (P.coproducts.{ν}).pushouts (f i))
  (emptySource : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
  (emptyTarget : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
  (hSource : IsColimit emptySource) (hTarget : IsColimit emptyTarget)

example : MorphismProperty.transfiniteCompositions.{max w w'}
    (P.coproducts.{ν}).pushouts (Limits.Sigma.map f) :=
  coproduct_mem P f hf emptySource emptyTarget hSource hTarget

end ActualCoproductArrow

section WholeCellularClass

variable {C : Type u} [Category.{v} C] (P : MorphismProperty C)
  [HasPushouts C] [HasCoproducts.{w} C]
  (emptySource : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
  (emptyTarget : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
  (hSource : IsColimit emptySource) (hTarget : IsColimit emptyTarget)

example : (MorphismProperty.transfiniteCompositions.{w}
    (P.coproducts.{ν}).pushouts).IsStableUnderCobaseChange ∧
    (MorphismProperty.transfiniteCompositions.{w}
      (P.coproducts.{ν}).pushouts).IsStableUnderCoproducts.{w} ∧
    MorphismProperty.IsStableUnderTransfiniteComposition.{w}
      (MorphismProperty.transfiniteCompositions.{w} (P.coproducts.{ν}).pushouts) :=
  cellularClosure_stable P emptySource emptyTarget hSource hTarget

end WholeCellularClass

#print axioms CategoryTheory.SmallObject.CellularNormalization.originalHistories_presentation
#print axioms CategoryTheory.SmallObject.CellularNormalization.transfiniteComposition_mem
#print axioms CategoryTheory.SmallObject.CellularNormalization.cellularClosure_stable

end CellularNormalizationClosurePublicUse
