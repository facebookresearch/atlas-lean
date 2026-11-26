/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentMixedFaceChart

/-!
# The original two-leg projection of the actual mixed Hom face

The actual negative-positive chart projects to the original positive
face by both supplied ordinal Hom maps. Its two outer endpoints and the
individual supplied middle vertex are retained literally.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.MixedFaceProjections
open SimplicialEnrichment HornBoxFaces HornInteriorFace HornHomFaces
variable {n : ℕ} (k : Interior.{u} n) (t : SourceInterior n)

/-- The original supplied left ordinal Hom map at the same zero and middle vertices. -/
def leftLeg : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 2))) (ULift.up.{u} t.val)) ⟶
    nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3))) (middle k t).val) :=
  retargetMap (coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex k)))
    (.mk (ULift.up (0 : Fin (n + 2)))) (.mk (ULift.up t.val))
    (congrArg SimplicialThickening.mk (ULift.ext (source_zero k))) rfl

/-- The original supplied right ordinal Hom map at the same middle and last vertices. -/
def rightLeg : nerve (SimplicialThickening.Path (ULift.up.{u} t.val) (ULift.up.{u} (Fin.last (n + 1)))) ⟶
    nerve (SimplicialThickening.Path (middle k t).val (ULift.up.{u} (Fin.last (n + 2)))) :=
  retargetMap (coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex k)))
    (.mk (ULift.up t.val)) (.mk (ULift.up (Fin.last (n + 1))))
    rfl (congrArg SimplicialThickening.mk (ULift.ext (target_last k)))

/-- The actual whole positive projection is given by the two original supplied face Hom maps and the
  original positive chart. -/
theorem positive_chart : (MixedFaceChart.chart k t).hom ≫ MixedFaceChart.positiveProjection k t =
    (leftLeg k t ⊗ₘ rightLeg k t) ≫
      (CompositionFace.positiveIso (ULift.up.{u} (0 : Fin (n + 3))) (middle k t).val
        (ULift.up.{u} (Fin.last (n + 2)))).hom := by
  apply (cancel_mono (CompositionFace.positive (ULift.up.{u} (0 : Fin (n + 3))) (middle k t).val
    (ULift.up.{u} (Fin.last (n + 2)))).ι).mp
  have hL := (Category.assoc (MixedFaceChart.chart k t).hom (MixedFaceChart.positiveProjection k t)
    (CompositionFace.positive (ULift.up.{u} (0 : Fin (n + 3))) (middle k t).val (ULift.up.{u} (Fin.last (n +
      2)))).ι).trans
      (congrArg (fun g => (MixedFaceChart.chart k t).hom ≫ g)
        (SSet.Subcomplex.homOfLE_ι (show MixedFaceChart.face k t ≤ _ from inf_le_right)))
  have hC : CompositionFace.composition (ULift.up.{u} (0 : Fin (n + 2))) (ULift.up.{u} t.val) (ULift.up.{u}
    (Fin.last (n + 1))) ≫
      (coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex k))).map
        (.mk (ULift.up (0 : Fin (n + 2)))) (.mk (ULift.up (Fin.last (n + 1)))) ≫
      eqToHom (congrArg₂ (fun a b : ULift.{u} (Fin (n + 3)) => nerve (SimplicialThickening.Path a b))
        (ULift.ext (source_zero k)) (ULift.ext (target_last k))) =
      (leftLeg k t ⊗ₘ rightLeg k t) ≫ CompositionFace.composition
        (ULift.up.{u} (0 : Fin (n + 3))) (middle k t).val (ULift.up.{u} (Fin.last (n + 2))) :=
    HornMapAlgebra.retargetMap_comp (coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex k)))
      (.mk (ULift.up (0 : Fin (n + 2)))) (.mk (ULift.up t.val)) (.mk (ULift.up (Fin.last (n + 1))))
      (congrArg SimplicialThickening.mk (ULift.ext (source_zero k))) rfl
      (congrArg SimplicialThickening.mk (ULift.ext (target_last k)))
  have hR := (Category.assoc (leftLeg k t ⊗ₘ rightLeg k t)
    (CompositionFace.positiveIso (ULift.up.{u} (0 : Fin (n + 3))) (middle k t).val (ULift.up.{u} (Fin.last
      (n + 2)))).hom
    (CompositionFace.positive (ULift.up.{u} (0 : Fin (n + 3))) (middle k t).val (ULift.up.{u} (Fin.last (n +
      2)))).ι).trans
      (congrArg (fun g => (leftLeg k t ⊗ₘ rightLeg k t) ≫ g)
        (CompositionFace.positiveIso_composition (ULift.up.{u} (0 : Fin (n + 3))) (middle k t).val
          (ULift.up.{u} (Fin.last (n + 2)))))
  exact hL.trans ((MixedFaceChart.chart_ambient k t).trans (hC.trans hR.symm))

end CategoryTheory.CoherentRealization.MixedFaceProjections
