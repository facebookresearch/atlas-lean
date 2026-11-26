/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeSimplicialWordLayers
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The actual original simplicial relative-word layer pushout

Each degree is the proved pointwise layer pushout on the same original
words. The evaluation functors jointly reflect colimits, so the entire
actual layer square is a simplicial pushout. The proof retains all
original labels, empty old-Hom stages, loop pairs and arbitrary words.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment

variable {O : Type u} {C : FixedObjects O}

/-- The actual whole simplicial layer square has this original pushout cocone. -/
def layerCocone (T : Data C) (x y : O) (n : ℕ) :
    PushoutCocone (boundaryLayerNormalize T x y n) (boundaryInclusion T x y n) :=
  PushoutCocone.mk (layerInclusion T x y n) (rawLayerNormalize T x y n) (simplicialLayer_square T x y n)

private def evaluatedLayerIsColimit (T : Data C) (x y : O) (n : ℕ) (q : SimplexCategoryᵒᵖ) :
    IsColimit (((@CategoryTheory.evaluation SimplexCategoryᵒᵖ inferInstance (Type u)
      (inferInstance : Category.{u} (Type u))).obj q).mapCocone (layerCocone T x y n)) := by
  let hp := @RelativeGenerators.layerIsPushout O (scalarCategory C q)
    (fun x y => (T.domain.Hom x y).obj q) (fun x y => (T.target.Hom x y).obj q)
    (fun {_ _} a => inclusionAt T q a) (fun {_ _} a => attachingAt T q a) x y n
  let E := (@CategoryTheory.evaluation SimplexCategoryᵒᵖ inferInstance (Type u)
    (inferInstance : Category.{u} (Type u))).obj q
  refine (IsColimit.equivOfNatIsoOfIso
    (spanCompIso E (boundaryLayerNormalize T x y n) (boundaryInclusion T x y n))
    (E.mapCocone (layerCocone T x y n)) hp.cocone
    (WalkingSpan.ext ?_ ?_ ?_)).symm hp.isColimit
  · exact Iso.refl _
  · exact (Category.comp_id _).trans (Category.id_comp _)
  · exact (Category.comp_id _).trans (Category.id_comp _)

/-- The actual original simplicial relative-word layer cocone is genuinely colimiting. -/
def layerCoconeIsColimit (T : Data C) (x y : O) (n : ℕ) : IsColimit (layerCocone T x y n) :=
  evaluationJointlyReflectsColimits (layerCocone T x y n) (evaluatedLayerIsColimit T x y n)

/-- The same entire original simplicial relative-word layer square is a genuine pushout. -/
theorem simplicialLayerIsPushout (T : Data C) (x y : O) (n : ℕ) :
    IsPushout (boundaryLayerNormalize T x y n) (boundaryInclusion T x y n)
      (layerInclusion T x y n) (rawLayerNormalize T x y n) :=
  IsPushout.of_isColimit (layerCoconeIsColimit T x y n)

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
