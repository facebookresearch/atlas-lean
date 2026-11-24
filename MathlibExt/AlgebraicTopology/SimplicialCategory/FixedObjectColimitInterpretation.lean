/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectDiagramGenerators

/-!
# Interpreting the actual fixed-object diagram presentation

Every original enriched cocone interprets the coproduct generators.
Its actual identity, composition and diagram equations prove all three
generating relations, so the existing presentation universal property
applies without a supplied colimit conclusion.
-/

noncomputable section
universe u v w
open CategoryTheory Limits MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.DiagramPresentation
open SimplicialQuiver

variable {O : Type u} {J : Type v} [Category.{w} J] [Small.{u} J]
  (F : J ⥤ FixedObjects O)

/-- The actual cocone maps interpret every original stage Hom generator. -/
def interpretation (s : Cocone F) : Interpretation (quiver F) s.pt.val where
  obj := vertex s.pt
  map x y := Sigma.desc (fun j : J => homMap (s.ι.app j) x y)

set_option backward.isDefEq.respectTransparency.types false in
/-- The whole generator interpretation reads back the same original cocone leg. -/
theorem stage_interpretation (s : Cocone F) (j : J) (x y : O) :
    stageHom F j x y ≫ (interpretation F s).map x y = homMap (s.ι.app j) x y := by
  change Sigma.ι (fun k : J => hom (F.obj k) x y) j ≫
      Sigma.desc (fun k : J => homMap (s.ι.app k) x y) = homMap (s.ι.app j) x y
  exact Sigma.ι_comp_desc (f := fun k : J => hom (F.obj k) x y)
    (P := hom s.pt x y) (fun k : J => homMap (D := s.pt) (s.ι.app k) x y) j

/-- Every original generating simplex evaluates by its actual enriched cocone map. -/
theorem interpretation_stage_eval (s : Cocone F) (j : J) (q : SimplexCategoryᵒᵖ)
    (x y : O) (a : (hom (F.obj j) x y).obj q) :
    (interpretation F s).evalPath q ((freeStageHom F j x y).app q a) =
      (homMap (s.ι.app j) x y).app q a :=
  (stage_eval F (interpretation F s) j q x y a).trans
    (congrArg (fun m => m.app q a) (stage_interpretation F s j x y))

set_option backward.isDefEq.respectTransparency.types false in
/-- The original cocone proves every identity, composition and diagram relation. -/
theorem interpretation_relations (s : Cocone F) (q : SimplexCategoryᵒᵖ) (x y : O)
    (p r : Path (quiver F) q x y) (h : relations F q x y p r) :
    (interpretation F s).evalPath q p = (interpretation F s).evalPath q r := by
  cases h with
  | identity j q x =>
      rw [interpretation_stage_eval, Interpretation.evalPath_nil]
      exact congrArg (fun m => m.app q PUnit.unit) (identityMap_homMap (s.ι.app j) x)
  | @composition j q x y z a b =>
      rw [interpretation_stage_eval, Interpretation.evalPath_comp,
        interpretation_stage_eval, interpretation_stage_eval]
      exact congrArg (fun m => m.app q (a, b)) (compositionMap_homMap (s.ι.app j) _ _ _)
  | @diagram j k f q x y a =>
      rw [interpretation_stage_eval, interpretation_stage_eval]
      have hm := congrArg (fun m => homMap m x y) (s.w f)
      rw [homMap_comp] at hm
      exact congrArg (fun m => m.app q a) hm.symm

end CategoryTheory.SimplicialEnrichment.FixedObjects.DiagramPresentation
