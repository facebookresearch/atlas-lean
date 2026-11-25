/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedLeftKanComponents

/-!
# Original whole-Hom evaluation of marked left-extension relations

Native free evaluation reads both relation maps on the entire original
marked Hom parameter. The index relation is the actual restricted
target action; the coefficient relation is the original source action.
No restriction to ordinary vertices or assumed Kan-extension map is
used in these equalities.
-/

noncomputable section
universe u v
open CategoryTheory

namespace SSet.Marked.EnrichedLeftKan

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable {C : Type u} [EnrichedCategory SSet.{u} C]
    {D : Type v} [EnrichedCategory SSet.{u} D]
    (j : EnrichedFunctor SSet.{u} C D) (W : EnrichedDiagram C)

/-- Evaluating the original index relation retains its whole index Hom map and actual object injection. -/
theorem indexRelation_evaluate (X : EnrichedDiagram D) (f : objectCoproduct j W ⟶ X) (x y : C) :
    enrichedFreeHomEquiv D (j.obj y) (prod (max (x ⟶[SSet.{u}] y)) (W.obj x)) X
        (indexRelation j W x y ≫ f) =
      prodMap (maximal.map (j.map x y)) (𝟙 (W.obj x)) ≫
        (EnrichedCoproduct.ι (objectFamily j W) x ≫ f).app (j.obj y) := by
  let i : enrichedFreeValue D (j.obj x) (j.obj y) (W.obj x) ⟶ (objectCoproduct j W).obj (j.obj y) :=
    (EnrichedCoproduct.ι (objectFamily j W) x).app (j.obj y)
  let a : prod (max (x ⟶[SSet.{u}] y)) (W.obj x) ⟶ (objectCoproduct j W).obj (j.obj y) :=
    prodMap (maximal.map (j.map x y)) (𝟙 (W.obj x)) ≫ i
  have h := enrichedFreeExtend_post D (j.obj y) (prod (max (x ⟶[SSet.{u}] y)) (W.obj x)) a f
  have he := congrArg
    (enrichedFreeHomEquiv D (j.obj y) (prod (max (x ⟶[SSet.{u}] y)) (W.obj x)) X) h
  exact he.trans ((enrichedFreeExtend_unit D (j.obj y)
    (prod (max (x ⟶[SSet.{u}] y)) (W.obj x)) X (a ≫ f.app (j.obj y))).trans (Category.assoc _ _ _))

/-- Whole original index-relation evaluation is exactly the restricted target action on the coefficient component. -/
theorem indexRelation_evaluate_action (X : EnrichedDiagram D) (f : objectCoproduct j W ⟶ X) (x y : C) :
    enrichedFreeHomEquiv D (j.obj y) (prod (max (x ⟶[SSet.{u}] y)) (W.obj x)) X
        (indexRelation j W x y ≫ f) =
      prodMap (𝟙 (max (x ⟶[SSet.{u}] y))) (componentEquiv j W X f x) ≫
        enrichedDiagramAction (j.comp SSet.{u} X) x y := by
  let a : W.obj x ⟶ X.obj (j.obj x) := componentEquiv j W X f x
  let t : enrichedFreeDiagram D (j.obj x) (W.obj x) ⟶ X :=
    EnrichedCoproduct.ι (objectFamily j W) x ≫ f
  have ht : t.app (j.obj y) =
      prodMap (𝟙 (max (j.obj x ⟶[SSet.{u}] j.obj y))) a ≫
        enrichedDiagramAction X (j.obj x) (j.obj y) :=
    enrichedFreeMap_component D (j.obj x) (W.obj x) X t (j.obj y)
  have hm : prodMap (maximal.map (j.map x y)) (𝟙 (W.obj x)) ≫
      prodMap (𝟙 (max (j.obj x ⟶[SSet.{u}] j.obj y))) a =
        prodMap (𝟙 (max (x ⟶[SSet.{u}] y))) a ≫
          prodMap (maximal.map (j.map x y)) (𝟙 (X.obj (j.obj x))) := by
    apply Hom.ext
    rfl
  exact (indexRelation_evaluate j W X f x y).trans
    ((congrArg (fun h => prodMap (maximal.map (j.map x y)) (𝟙 (W.obj x)) ≫ h) ht).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun h => h ≫ enrichedDiagramAction X (j.obj x) (j.obj y)) hm).trans
          ((Category.assoc _ _ _).trans
            (congrArg (fun h => prodMap (𝟙 (max (x ⟶[SSet.{u}] y))) a ≫ h)
              (enrichedDiagramAction_restriction j X x y).symm)))))

/-- Whole evaluation of the original action relation is the same source action followed by its original
  coefficient component. -/
theorem actionRelation_evaluate (X : EnrichedDiagram D) (f : objectCoproduct j W ⟶ X) (x y : C) :
    enrichedFreeHomEquiv D (j.obj y) (prod (max (x ⟶[SSet.{u}] y)) (W.obj x)) X
        (actionRelation j W x y ≫ f) =
      enrichedDiagramAction W x y ≫ componentEquiv j W X f y := by
  let i : enrichedFreeValue D (j.obj y) (j.obj y) (W.obj y) ⟶ (objectCoproduct j W).obj (j.obj y) :=
    (EnrichedCoproduct.ι (objectFamily j W) y).app (j.obj y)
  let a : prod (max (x ⟶[SSet.{u}] y)) (W.obj x) ⟶ (objectCoproduct j W).obj (j.obj y) :=
    enrichedDiagramAction W x y ≫ (enrichedFreeUnit D (j.obj y) (W.obj y) ≫ i)
  have h := enrichedFreeExtend_post D (j.obj y) (prod (max (x ⟶[SSet.{u}] y)) (W.obj x)) a f
  have he := congrArg
    (enrichedFreeHomEquiv D (j.obj y) (prod (max (x ⟶[SSet.{u}] y)) (W.obj x)) X) h
  have hc : (enrichedFreeUnit D (j.obj y) (W.obj y) ≫ i) ≫ f.app (j.obj y) =
      componentEquiv j W X f y :=
    (Category.assoc _ _ _).trans (componentEquiv_apply j W X f y).symm
  exact he.trans ((enrichedFreeExtend_unit D (j.obj y)
    (prod (max (x ⟶[SSet.{u}] y)) (W.obj x)) X (a ≫ f.app (j.obj y))).trans
      ((Category.assoc _ _ _).trans (congrArg (fun h => enrichedDiagramAction W x y ≫ h) hc)))

/-- The whole coproduct relation equation is equivalent to each entire original marked parameter relation. -/
theorem relation_eq_iff (X : EnrichedDiagram D) (f : objectCoproduct j W ⟶ X) :
    (leftRelation j W ≫ f = rightRelation j W ≫ f) ↔
      ∀ x y : C, indexRelation j W x y ≫ f = actionRelation j W x y ≫ f := by
  constructor
  · intro h x y
    let i := EnrichedCoproduct.ι (relationFamily j W) (x, y)
    exact (congrArg (fun t => t ≫ f) (relation_ι_left j W x y)).symm.trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t => i ≫ t) h).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun t => t ≫ f) (relation_ι_right j W x y)))))
  · intro h
    apply EnrichedCoproduct.hom_ext (relationFamily j W)
    rintro ⟨x, y⟩
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ f) (relation_ι_left j W x y)).trans
        ((h x y).trans
          ((congrArg (fun t => t ≫ f) (relation_ι_right j W x y)).symm.trans
            (Category.assoc _ _ _))))

/-- The actual entire index/action relation equation is precisely full marked naturality of the original components. -/
theorem relation_eq_iff_natural (X : EnrichedDiagram D) (f : objectCoproduct j W ⟶ X) :
    (leftRelation j W ≫ f = rightRelation j W ≫ f) ↔ NaturalComponents j W X (componentEquiv j W X f) := by
  rw [relation_eq_iff]
  constructor
  · intro h x y
    have he := congrArg
      (enrichedFreeHomEquiv D (j.obj y) (prod (max (x ⟶[SSet.{u}] y)) (W.obj x)) X) (h x y)
    exact (actionRelation_evaluate j W X f x y).symm.trans
      (he.symm.trans (indexRelation_evaluate_action j W X f x y))
  · intro h x y
    apply (enrichedFreeHomEquiv D (j.obj y) (prod (max (x ⟶[SSet.{u}] y)) (W.obj x)) X).injective
    exact (indexRelation_evaluate_action j W X f x y).trans
      ((h x y).symm.trans (actionRelation_evaluate j W X f x y).symm)

end SSet.Marked.EnrichedLeftKan
