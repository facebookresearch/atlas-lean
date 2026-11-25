/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedLeftKanRelationEvaluation

/-!
# The actual full marked enriched left-extension Hom correspondence

The original coequalizer Hom correspondence, full free evaluations and
whole action-relation theorem construct the actual universal Hom
equivalence. Every component reads the original free unit, summand and
coequalizer projection. Target naturality retains those same maps; no
adjunction or Kan-extension outcome is an input.
-/

noncomputable section
universe u v
open CategoryTheory

namespace SSet.Marked.EnrichedLeftKan

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable {C : Type u} [EnrichedCategory SSet.{u} C]
    {D : Type v} [EnrichedCategory SSet.{u} D]
    (j : EnrichedFunctor SSet.{u} C D) (W : EnrichedDiagram C)

/-- Whole original coequalizer relations give the genuine full marked enriched left-extension Hom equivalence. -/
def universalHomEquiv (X : EnrichedDiagram D) :
    (object j W ⟶ X) ≃ (W ⟶ j.comp SSet.{u} X) :=
  (homEquiv j W X).trans
    ((Equiv.subtypeEquiv (componentEquiv j W X)
      (fun f => relation_eq_iff_natural j W X f)).trans (naturalComponentEquiv j W X).symm)

/-- Each whole universal component is the original unit evaluation after the original summand and map. -/
theorem universalHomEquiv_app (X : EnrichedDiagram D) (f : object j W ⟶ X) (x : C) :
    (universalHomEquiv j W X f).app x =
      enrichedFreeUnit D (j.obj x) (W.obj x) ≫ (summand j W x ≫ f).app (j.obj x) := by
  change enrichedFreeUnit D (j.obj x) (W.obj x) ≫
      (EnrichedCoproduct.ι (objectFamily j W) x ≫ (π j W ≫ f)).app (j.obj x) =
    enrichedFreeUnit D (j.obj x) (W.obj x) ≫
      ((EnrichedCoproduct.ι (objectFamily j W) x ≫ π j W) ≫ f).app (j.obj x)
  exact congrArg (fun t => enrichedFreeUnit D (j.obj x) (W.obj x) ≫ t.app (j.obj x))
    (Category.assoc (EnrichedCoproduct.ι (objectFamily j W) x) (π j W) f).symm

/-- The actual universal Hom correspondence is natural in whole original marked target maps. -/
theorem universalHomEquiv_natural_right {X Y : EnrichedDiagram D}
    (f : object j W ⟶ X) (g : X ⟶ Y) :
    universalHomEquiv j W Y (f ≫ g) =
      universalHomEquiv j W X f ≫ (enrichedDiagramRestrict j).map g := by
  apply EnrichedDiagramMap.ext
  funext x
  have hx := universalHomEquiv_app j W X f x
  have hy := universalHomEquiv_app j W Y (f ≫ g) x
  have hs := congrArg (fun t => t.app (j.obj x)) (Category.assoc (summand j W x) f g)
  exact hy.trans
    ((congrArg (fun t => enrichedFreeUnit D (j.obj x) (W.obj x) ≫ t) hs.symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ g.app (j.obj x)) hx.symm)))

end SSet.Marked.EnrichedLeftKan
