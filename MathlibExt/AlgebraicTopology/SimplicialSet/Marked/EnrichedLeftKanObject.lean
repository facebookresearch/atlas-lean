/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedLeftKanRelations
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# The actual marked enriched left-extension coequalizer

The object is the native coequalizer of the original whole index and
coefficient-action relations. Its injection and Hom correspondence are
the actual categorical coequalizer maps. All component data retain the
original source objects, Hom parameters and coefficient markings.
-/

noncomputable section
universe u v
open CategoryTheory Limits

namespace SSet.Marked.EnrichedLeftKan

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory EnrichedColimit.hasColimits

variable {C : Type u} [EnrichedCategory SSet.{u} C]
    {D : Type v} [EnrichedCategory SSet.{u} D]
    (j : EnrichedFunctor SSet.{u} C D) (W : EnrichedDiagram C)

local instance relationHasCoequalizer : HasCoequalizer (leftRelation j W) (rightRelation j W) := by
  let _ : ∀ x : D, HasColimit
      (EnrichedColimit.evaluated (parallelPair (leftRelation j W) (rightRelation j W)) x) :=
    fun _ => inferInstance
  exact EnrichedColimit.hasColimit (parallelPair (leftRelation j W) (rightRelation j W))

/-- The whole marked enriched left-extension object is the actual coequalizer of its original relations. -/
def object : EnrichedDiagram D := coequalizer (leftRelation j W) (rightRelation j W)

/-- The native object-coproduct injection keeps the actual selected coequalizer map. -/
def π : objectCoproduct j W ⟶ object j W := coequalizer.π (leftRelation j W) (rightRelation j W)

/-- Every original whole index and action relation is identified by the same native coequalizer projection. -/
theorem condition : leftRelation j W ≫ π j W = rightRelation j W ≫ π j W :=
  coequalizer.condition _ _

/-- The original source coefficient summand maps through its actual full enriched injection and coequalizer. -/
def summand (x : C) : objectFamily j W x ⟶ object j W :=
  EnrichedCoproduct.ι (objectFamily j W) x ≫ π j W

/-- Native coequalizer maps correspond to whole marked maps satisfying the actual original relations. -/
def homEquiv (X : EnrichedDiagram D) :
    (object j W ⟶ X) ≃
      {f : objectCoproduct j W ⟶ X // leftRelation j W ≫ f = rightRelation j W ≫ f} :=
  Cofork.IsColimit.homIso (coequalizerIsCoequalizer (leftRelation j W) (rightRelation j W)) X

/-- The forward Hom correspondence uses exactly the original selected coequalizer projection. -/
theorem homEquiv_apply (X : EnrichedDiagram D) (f : object j W ⟶ X) :
    (homEquiv j W X f).val = π j W ≫ f := rfl

end SSet.Marked.EnrichedLeftKan
