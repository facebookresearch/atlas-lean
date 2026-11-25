/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedFreeDiagram
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedDiagramAction

/-!
# The genuine free enriched diagram and evaluation adjunction

The unit inserts the original enriched identity, and extension acts by
the original whole Hom prism. Full enriched naturality proves that each
map from the free diagram is determined by its original value at the
specified object. Both inverse laws and the two whole adjunction
triangles are proved; no adjunction or model outcome is an input.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable (C : Type v) [EnrichedCategory SSet.{u} C]

/-- The genuine free-diagram unit inserts the actual enriched identity and keeps the coefficient. -/
def enrichedFreeUnit (c : C) (A : Marked.{u}) : A ⟶ enrichedFreeValue C c c A :=
  prodLift (toMax (CartesianMonoidalCategory.toUnit A.toSSet ≫ eId SSet.{u} c)) (𝟙 A)

/-- Acting in the free diagram is exactly the original enriched composition prism. -/
theorem enrichedFreeDiagram_action (c x y : C) (A : Marked.{u}) :
    enrichedDiagramAction (enrichedFreeDiagram C c A) x y = enrichedFreeActionPrism C c x y A :=
  maxUncurry_maxCurry _

/-- Inserting the original enriched identity and acting recovers the entire free value. -/
theorem enrichedFreeUnit_action (c x : C) (A : Marked.{u}) :
    prodMap (𝟙 (max (c ⟶[SSet.{u}] x))) (enrichedFreeUnit C c A) ≫
      enrichedDiagramAction (enrichedFreeDiagram C c A) c x =
        𝟙 (enrichedFreeValue C c x A) := by
  rw [enrichedFreeDiagram_action]
  apply Hom.ext
  ext q z
  apply Prod.ext
  · exact congr($(e_id_comp SSet.{u} c x).app q z.1)
  · rfl

/-- Extension is the original whole marked action on the supplied coefficient map. -/
def enrichedFreeExtend (c : C) (A : Marked.{u}) (F : EnrichedDiagram C) (f : A ⟶ F.obj c) :
    enrichedFreeDiagram C c A ⟶ F where
  app x := prodMap (𝟙 (max (c ⟶[SSet.{u}] x))) f ≫ enrichedDiagramAction F c x
  naturality x y := by
    ext n h
    apply Hom.ext
    ext q a
    change (enrichedDiagramAction F c y).hom.app q
        ((eComp SSet.{u} c x y).app q
          (a.2.1, (SSet.yonedaEquiv.symm h).app q a.1), f.hom.app q a.2.2) =
      ((F.map x y).app n h).hom.app q
        (a.1, (enrichedDiagramAction F c x).hom.app q (a.2.1, f.hom.app q a.2.2))
    exact (enrichedDiagramAction_comp F c x y q a.2.1
      ((SSet.yonedaEquiv.symm h).app q a.1) (f.hom.app q a.2.2)).trans
        (enrichedDiagramAction_restrict F x y n q h a.1 _).symm

/-- Evaluation of the genuine extension along the original unit is the supplied coefficient map. -/
theorem enrichedFreeExtend_unit (c : C) (A : Marked.{u}) (F : EnrichedDiagram C)
    (f : A ⟶ F.obj c) :
    enrichedFreeUnit C c A ≫ (enrichedFreeExtend C c A F f).app c = f := by
  apply Hom.ext
  ext q a
  exact enrichedDiagramAction_id F c q (f.hom.app q a)

/-- Full enriched naturality reconstructs the whole original diagram map from its unit evaluation. -/
theorem enrichedFreeExtend_recover (c : C) (A : Marked.{u}) (F : EnrichedDiagram C)
    (α : enrichedFreeDiagram C c A ⟶ F) :
    enrichedFreeExtend C c A F (enrichedFreeUnit C c A ≫ α.app c) = α := by
  apply EnrichedDiagramMap.ext
  funext x
  have h := congrArg
    (fun t => prodMap (𝟙 (max (c ⟶[SSet.{u}] x))) (enrichedFreeUnit C c A) ≫ t)
    (enrichedDiagramAction_natural α c x)
  have hm : prodMap (𝟙 (max (c ⟶[SSet.{u}] x))) (enrichedFreeUnit C c A) ≫
      prodMap (𝟙 (max (c ⟶[SSet.{u}] x))) (α.app c) =
        prodMap (𝟙 (max (c ⟶[SSet.{u}] x))) (enrichedFreeUnit C c A ≫ α.app c) :=
    (prodMap_comp (𝟙 _) (𝟙 _) (enrichedFreeUnit C c A) (α.app c)).symm
  have hl : prodMap (𝟙 (max (c ⟶[SSet.{u}] x))) (enrichedFreeUnit C c A) ≫
      (enrichedDiagramAction (enrichedFreeDiagram C c A) c x ≫ α.app x) = α.app x := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ α.app x) (enrichedFreeUnit_action C c x A)).trans
        (Category.id_comp (α.app x)))
  have hr : prodMap (𝟙 (max (c ⟶[SSet.{u}] x))) (enrichedFreeUnit C c A) ≫
      (prodMap (𝟙 (max (c ⟶[SSet.{u}] x))) (α.app c) ≫ enrichedDiagramAction F c x) =
        (enrichedFreeExtend C c A F (enrichedFreeUnit C c A ≫ α.app c)).app x := by
    rw [← Category.assoc, hm]
    rfl
  exact hr.symm.trans (h.symm.trans hl)

/-- The free enriched diagram represents actual evaluation at the specified original object. -/
def enrichedFreeHomEquiv (c : C) (A : Marked.{u}) (F : EnrichedDiagram C) :
    (enrichedFreeDiagram C c A ⟶ F) ≃ (A ⟶ F.obj c) where
  toFun α := enrichedFreeUnit C c A ≫ α.app c
  invFun := enrichedFreeExtend C c A F
  left_inv := enrichedFreeExtend_recover C c A F
  right_inv := enrichedFreeExtend_unit C c A F

/-- Actual free enriched diagrams are left adjoint to the original coefficient evaluation. -/
def enrichedFreeEvaluationAdjunction (c : C) :
    enrichedFreeDiagramFunctor C c ⊣ enrichedDiagramEvaluation C c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := enrichedFreeHomEquiv C c
      homEquiv_naturality_left_symm := by
        intro A' A F f g
        apply EnrichedDiagramMap.ext
        funext x
        change prodMap (𝟙 (max (c ⟶[SSet.{u}] x))) (f ≫ g) ≫ enrichedDiagramAction F c x =
          prodMap (𝟙 (max (c ⟶[SSet.{u}] x))) f ≫
            (prodMap (𝟙 (max (c ⟶[SSet.{u}] x))) g ≫ enrichedDiagramAction F c x)
        exact (congrArg (fun t => t ≫ enrichedDiagramAction F c x)
          (prodMap_comp (𝟙 (max (c ⟶[SSet.{u}] x))) (𝟙 (max (c ⟶[SSet.{u}] x))) f g)).trans
            (Category.assoc _ _ _)
      homEquiv_naturality_right := by
        intro A F G f g
        change enrichedFreeUnit C c A ≫ (f.app c ≫ g.app c) =
          (enrichedFreeUnit C c A ≫ f.app c) ≫ g.app c
        exact (Category.assoc _ _ _).symm }

/-- The adjunction unit is exactly insertion of the original enriched identity. -/
theorem enrichedFreeEvaluationAdjunction_unit (c : C) (A : Marked.{u}) :
    (enrichedFreeEvaluationAdjunction C c).unit.app A = enrichedFreeUnit C c A := by
  change enrichedFreeHomEquiv C c A (enrichedFreeDiagram C c A) (𝟙 _) = _
  exact Category.comp_id (enrichedFreeUnit C c A)

/-- The adjunction counit is precisely the original whole-action extension of the identity. -/
theorem enrichedFreeEvaluationAdjunction_counit (c : C) (F : EnrichedDiagram C) :
    (enrichedFreeEvaluationAdjunction C c).counit.app F =
      enrichedFreeExtend C c (F.obj c) F (𝟙 (F.obj c)) := rfl

/-- The full free-diagram triangle retains all original marked components and Hom actions. -/
theorem enrichedFreeEvaluation_left_triangle (c : C) (A : Marked.{u}) :
    (enrichedFreeDiagramFunctor C c).map ((enrichedFreeEvaluationAdjunction C c).unit.app A) ≫
      (enrichedFreeEvaluationAdjunction C c).counit.app ((enrichedFreeDiagramFunctor C c).obj A) =
        𝟙 _ :=
  (enrichedFreeEvaluationAdjunction C c).left_triangle_components A

/-- The whole original evaluation triangle is the coefficient identity. -/
theorem enrichedFreeEvaluation_right_triangle (c : C) (F : EnrichedDiagram C) :
    (enrichedFreeEvaluationAdjunction C c).unit.app ((enrichedDiagramEvaluation C c).obj F) ≫
      (enrichedDiagramEvaluation C c).map ((enrichedFreeEvaluationAdjunction C c).counit.app F) =
        𝟙 _ :=
  (enrichedFreeEvaluationAdjunction C c).right_triangle_components F

end SSet.Marked
