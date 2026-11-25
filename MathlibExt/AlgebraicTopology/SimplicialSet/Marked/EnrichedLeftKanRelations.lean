/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedCoproduct
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedFreeEvaluation

/-!
# The native whole-Hom relations for marked enriched left extension

The object summands are free diagrams on the original coefficient
values. A relation summand retains the entire original source Hom
parameter and coefficient. Its two actual maps are the index Hom map
and the original coefficient action, extended through the genuine
free evaluation adjunction. No enriched Kan-extension outcome is used.
-/

noncomputable section
universe u v
open CategoryTheory Limits

namespace SSet.Marked.EnrichedLeftKan

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable {C : Type u} [EnrichedCategory SSet.{u} C]
    {D : Type v} [EnrichedCategory SSet.{u} D]
    (j : EnrichedFunctor SSet.{u} C D) (W : EnrichedDiagram C)

/-- Original source objects give actual free marked coefficient summands at their original index images. -/
def objectFamily (x : C) : EnrichedDiagram D := enrichedFreeDiagram D (j.obj x) (W.obj x)

/-- Each relation retains the whole original source Hom parameter and original coefficient object. -/
def relationFamily (p : C × C) : EnrichedDiagram D :=
  enrichedFreeDiagram D (j.obj p.2) (prod (max (p.1 ⟶[SSet.{u}] p.2)) (W.obj p.1))

/-- The original object summands form the actual full marked enriched coproduct. -/
def objectCoproduct : EnrichedDiagram D := EnrichedCoproduct.object (objectFamily j W)

/-- The whole original Hom relations form their genuine marked enriched coproduct. -/
def relationCoproduct : EnrichedDiagram D := EnrichedCoproduct.object (relationFamily j W)

/-- The first relation map retains the actual original index Hom map and coefficient identity. -/
def indexRelation (x y : C) : relationFamily j W (x, y) ⟶ objectCoproduct j W := by
  let i : enrichedFreeValue D (j.obj x) (j.obj y) (W.obj x) ⟶ (objectCoproduct j W).obj (j.obj y) :=
    (EnrichedCoproduct.ι (objectFamily j W) x).app (j.obj y)
  exact enrichedFreeExtend D (j.obj y) (prod (max (x ⟶[SSet.{u}] y)) (W.obj x))
    (objectCoproduct j W) (prodMap (maximal.map (j.map x y)) (𝟙 (W.obj x)) ≫ i)

/-- The second relation map is the original coefficient action followed by its genuine free unit and object
  injection. -/
def actionRelation (x y : C) : relationFamily j W (x, y) ⟶ objectCoproduct j W := by
  let i : enrichedFreeValue D (j.obj y) (j.obj y) (W.obj y) ⟶ (objectCoproduct j W).obj (j.obj y) :=
    (EnrichedCoproduct.ι (objectFamily j W) y).app (j.obj y)
  exact enrichedFreeExtend D (j.obj y) (prod (max (x ⟶[SSet.{u}] y)) (W.obj x))
    (objectCoproduct j W)
      (enrichedDiagramAction W x y ≫ (enrichedFreeUnit D (j.obj y) (W.obj y) ≫ i))

/-- The whole original index relations descend through the actual relation coproduct. -/
def leftRelation : relationCoproduct j W ⟶ objectCoproduct j W :=
  EnrichedCoproduct.desc (relationFamily j W) (fun p => indexRelation j W p.1 p.2)

/-- The entire original action relations have the same genuine enriched coproduct descent. -/
def rightRelation : relationCoproduct j W ⟶ objectCoproduct j W :=
  EnrichedCoproduct.desc (relationFamily j W) (fun p => actionRelation j W p.1 p.2)

/-- The original relation injection recovers precisely its whole index Hom relation. -/
theorem relation_ι_left (x y : C) :
    EnrichedCoproduct.ι (relationFamily j W) (x, y) ≫ leftRelation j W = indexRelation j W x y :=
  EnrichedCoproduct.ι_desc (relationFamily j W) _ (x, y)

/-- The same relation injection recovers the original coefficient action relation. -/
theorem relation_ι_right (x y : C) :
    EnrichedCoproduct.ι (relationFamily j W) (x, y) ≫ rightRelation j W = actionRelation j W x y :=
  EnrichedCoproduct.ι_desc (relationFamily j W) _ (x, y)

end SSet.Marked.EnrichedLeftKan
