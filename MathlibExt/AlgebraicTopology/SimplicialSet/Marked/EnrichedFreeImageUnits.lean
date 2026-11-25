/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedLeftKanFreeIso

/-!
# Exact original unit formulas for native free left-extension images

The genuine free-image isomorphism is defined by actual original
left-extension and free/evaluation universal correspondences. Its
inverse followed by any whole target map reads the same original
coefficient unit map. This exposes native comparison maps for the
boundary attachment argument without a representing outcome input.
-/

noncomputable section
universe u v
open CategoryTheory Limits Opposite

namespace SSet.Marked
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable {C : Type u} [EnrichedCategory SSet.{u} C]
  {D : Type v} [EnrichedCategory SSet.{u} D]
  (j : EnrichedFunctor SSet.{u} C D) (c : C) (A : Marked.{u})

/-- The actual original free image comparison inverse retains the original coefficient unit in the native
  left-extension Hom correspondence. -/
theorem enrichedLeftKanFreeIso_inv_unit :
    enrichedFreeHomEquiv D (j.obj c) A (EnrichedLeftKan.object j (enrichedFreeDiagram C c A))
      (enrichedLeftKanFreeIso j c A).inv =
      enrichedFreeHomEquiv C c A ((enrichedDiagramRestrict j).obj
        (EnrichedLeftKan.object j (enrichedFreeDiagram C c A)))
          (EnrichedLeftKan.unit j (enrichedFreeDiagram C c A)) := by
  change enrichedFreeHomEquiv D (j.obj c) A _
    ((enrichedFreeHomEquiv D (j.obj c) A _).symm
      (enrichedFreeHomEquiv C c A _
        (EnrichedLeftKan.universalHomEquiv j (enrichedFreeDiagram C c A) _ (𝟙 _)))) = _
  exact (enrichedFreeHomEquiv D (j.obj c) A (EnrichedLeftKan.object j (enrichedFreeDiagram C c A))).apply_symm_apply
    (enrichedFreeHomEquiv C c A ((enrichedDiagramRestrict j).obj
      (EnrichedLeftKan.object j (enrichedFreeDiagram C c A)))
        (EnrichedLeftKan.unit j (enrichedFreeDiagram C c A)))

/-- The actual native inverse free-image mate and a whole target map read precisely the same original
  coefficient after the native left-extension universal map. -/
theorem enrichedLeftKanFreeIso_inv_post {F : EnrichedDiagram D}
    (f : EnrichedLeftKan.object j (enrichedFreeDiagram C c A) ⟶ F) :
    enrichedFreeHomEquiv D (j.obj c) A F ((enrichedLeftKanFreeIso j c A).inv ≫ f) =
      enrichedFreeHomEquiv C c A ((enrichedDiagramRestrict j).obj F)
        (EnrichedLeftKan.universalHomEquiv j (enrichedFreeDiagram C c A) F f) := by
  have h := (enrichedImageFreeCorepresenter j c A).homEquiv_comp f (enrichedLeftKanFreeIso j c A).inv
  have h' := (enrichedLeftKanFreeCorepresenter j c A).homEquiv_comp f (𝟙 _)
  rw [Category.id_comp] at h'
  exact h.trans ((congrArg (fun g => g ≫ f.app (j.obj c)) (enrichedLeftKanFreeIso_inv_unit j c A)).trans h'.symm)

end SSet.Marked
