/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedLeftKanObject
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedCoproductHom
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedFreeNaturality
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedActionNaturality

/-!
# Original components of the actual marked left-extension universal maps

The original object coproduct Hom correspondence and native free
evaluation identify its maps with original marked coefficient
components. Full action equations correspond to whole enriched
naturality, without restricting tests to ordinary vertices.
-/

noncomputable section
universe u v
open CategoryTheory

namespace SSet.Marked.EnrichedLeftKan

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable {C : Type u} [EnrichedCategory SSet.{u} C]
    {D : Type v} [EnrichedCategory SSet.{u} D]
    (j : EnrichedFunctor SSet.{u} C D) (W : EnrichedDiagram C)

/-- Original object-coproduct maps correspond to their whole marked coefficient evaluations. -/
def componentEquiv (X : EnrichedDiagram D) :
    (objectCoproduct j W ⟶ X) ≃ (∀ x : C, W.obj x ⟶ X.obj (j.obj x)) :=
  (EnrichedCoproduct.homEquiv (objectFamily j W) X).trans
    (Equiv.piCongrRight (fun x => enrichedFreeHomEquiv D (j.obj x) (W.obj x) X))

/-- Each original component is its native free-unit evaluation after the original object injection. -/
theorem componentEquiv_apply (X : EnrichedDiagram D) (f : objectCoproduct j W ⟶ X) (x : C) :
    componentEquiv j W X f x = enrichedFreeUnit D (j.obj x) (W.obj x) ≫
      (EnrichedCoproduct.ι (objectFamily j W) x ≫ f).app (j.obj x) := rfl

/-- Whole marked action naturality is the exact original component condition for the left extension. -/
def NaturalComponents (X : EnrichedDiagram D) (a : ∀ x : C, W.obj x ⟶ X.obj (j.obj x)) : Prop :=
  ∀ x y : C, enrichedDiagramAction W x y ≫ a y =
    prodMap (𝟙 (max (x ⟶[SSet.{u}] y))) (a x) ≫
      enrichedDiagramAction (j.comp SSet.{u} X) x y

/-- Genuine full enriched maps correspond to exactly the same whole original marked action equations. -/
def naturalComponentEquiv (X : EnrichedDiagram D) :
    (W ⟶ j.comp SSet.{u} X) ≃
      {a : ∀ x : C, W.obj x ⟶ X.obj (j.obj x) // NaturalComponents j W X a} where
  toFun f := ⟨f.app, enrichedDiagramAction_natural f⟩
  invFun f := EnrichedDiagramMap.ofAction f.val f.property
  left_inv f := by
    apply EnrichedDiagramMap.ext
    change f.app = f.app
    rfl
  right_inv f := by
    apply Subtype.ext
    change f.val = f.val
    rfl

end SSet.Marked.EnrichedLeftKan
