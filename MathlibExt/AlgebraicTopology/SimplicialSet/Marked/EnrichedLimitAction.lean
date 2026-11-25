/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedDiagramAction
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedActionNaturality
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SmallLimits

/-!
# Whole native Hom actions on marked enriched pointwise limits

The value at each original object is its actual marked limit. The
whole enriched action is the unique marked map with all the original
component actions as projections. The projection equations expose
all original scalar simplices and marks. No diagram model is assumed.
-/

noncomputable section
universe u v w t
open CategoryTheory Limits Opposite

namespace SSet.Marked.EnrichedLimit

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable {C : Type v} [EnrichedCategory SSet.{u} C]
    {J : Type w} [Category.{t} J] (K : J ⥤ EnrichedDiagram C)

/-- Original marked values at the specified enriched source object. -/
abbrev evaluated (x : C) : J ⥤ Marked.{u} := K ⋙ enrichedDiagramEvaluation C x

/-- The whole original marked action cone uses the actual source projections and component Hom actions. -/
def actionCone (x y : C) [HasLimit (evaluated K x)] : Cone (evaluated K y) where
  pt := prod (max (x ⟶[SSet.{u}] y)) (limit (evaluated K x))
  π :=
    { app j := prodMap (𝟙 (max (x ⟶[SSet.{u}] y))) (limit.π (evaluated K x) j) ≫
        enrichedDiagramAction (K.obj j) x y
      naturality i j f := by
        let px : limit (evaluated K x) ⟶ (K.obj i).obj x := limit.π (evaluated K x) i
        let qx : limit (evaluated K x) ⟶ (K.obj j).obj x := limit.π (evaluated K x) j
        have hn := enrichedDiagramAction_natural (K.map f) x y
        have hp : px ≫ (K.map f).app x = qx := limit.w (evaluated K x) f
        have hm : prodMap (𝟙 (max (x ⟶[SSet.{u}] y))) px ≫
            prodMap (𝟙 (max (x ⟶[SSet.{u}] y))) ((K.map f).app x) =
              prodMap (𝟙 (max (x ⟶[SSet.{u}] y))) qx := by
          exact (prodMap_comp (𝟙 _) (𝟙 _) px ((K.map f).app x)).symm.trans
            (congrArg (fun t => prodMap (𝟙 (max (x ⟶[SSet.{u}] y))) t) hp)
        symm
        exact (Category.assoc _ _ _).trans
          ((congrArg (fun t => prodMap (𝟙 (max (x ⟶[SSet.{u}] y))) px ≫ t) hn).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (fun t => t ≫ enrichedDiagramAction (K.obj j) x y) hm).trans
                (Category.id_comp _).symm))) }

/-- The native marked limit action is the genuine marked cone lift, with the original projections. -/
def action (x y : C) [HasLimit (evaluated K x)] [HasLimit (evaluated K y)] :
    prod (max (x ⟶[SSet.{u}] y)) (limit (evaluated K x)) ⟶ limit (evaluated K y) :=
  limit.lift (evaluated K y) (actionCone K x y)

/-- Every original target projection retains its whole component action and actual source projection. -/
theorem action_projection (x y : C) [HasLimit (evaluated K x)] [HasLimit (evaluated K y)] (j : J) :
    action K x y ≫ limit.π (evaluated K y) j =
      prodMap (𝟙 (max (x ⟶[SSet.{u}] y))) (limit.π (evaluated K x) j) ≫
        enrichedDiagramAction (K.obj j) x y := limit.lift_π (actionCone K x y) j

/-- Original projections commute with every whole native enriched Hom simplex. -/
theorem projection_fullMap (x y : C) [HasLimit (evaluated K x)] [HasLimit (evaluated K y)] (j : J) :
    maxCurry (action K x y) ≫ mappingComplexPost .maximal (limit (evaluated K x))
        (limit.π (evaluated K y) j) =
      (K.obj j).map x y ≫ mappingComplexPre .maximal (limit.π (evaluated K x) j) ((K.obj j).obj y) := by
  let px : limit (evaluated K x) ⟶ (K.obj j).obj x := limit.π (evaluated K x) j
  let py : limit (evaluated K y) ⟶ (K.obj j).obj y := limit.π (evaluated K y) j
  exact (maxCurry_post (action K x y) py).symm.trans
    ((congrArg maxCurry (action_projection K x y j)).trans
      ((maxCurry_source px (enrichedDiagramAction (K.obj j) x y)).trans
        (congrArg (fun t => t ≫ mappingComplexPre .maximal px ((K.obj j).obj y))
          (maxCurry_maxUncurry ((K.obj j).map x y)))))

/-- All original marked target projections detect an entire simplicial Hom map in every scalar degree. -/
theorem targetMap_hom_ext (y : C) [HasLimit (evaluated K y)] (A : SSet.{u}) (T : Marked.{u})
    {f g : A ⟶ mappingComplex .maximal T (limit (evaluated K y))}
    (h : ∀ j : J, f ≫ mappingComplexPost .maximal T (limit.π (evaluated K y) j) =
      g ≫ mappingComplexPost .maximal T (limit.π (evaluated K y) j)) : f = g := by
  ext n a
  apply limit.hom_ext
  intro j
  exact congr($(h j).app n a)

end SSet.Marked.EnrichedLimit
