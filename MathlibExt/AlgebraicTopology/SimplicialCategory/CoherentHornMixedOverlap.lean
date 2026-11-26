/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentMixedFaceProjections
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornShortFaceRestrictions

/-!
# Actual supplied-horn agreement on the whole mixed Hom face

Both projections of the genuine mixed chart read the supplied original
face functor. The short-leg restrictions and its whole enriched
composition law prove agreement without any filler or compatibility
outcome as input.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HornMixedOverlap
open SimplicialEnrichment HornBoxFaces HornInteriorFace HornHomFaces
variable {C : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2)) (k : Interior.{u} n)
  (t : SourceInterior n) (hk : HornBoxFaces.vertex k ≠ i)

/-- The entire left leg of the mixed chart reads the actual supplied face Hom map. -/
theorem left_readback : MixedFaceProjections.leftLeg k t ≫ leftMap f hi₀ hiₙ (middle k t) =
    retargetMap (HornFaces.faceFunctor f (HornBoxFaces.vertex k) hk)
      (.mk (ULift.up (0 : Fin (n + 2)))) (.mk (ULift.up t.val))
      ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans (congrArg (HornFaces.object f) (source_zero k)))
      (HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _) := by
  change ((coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex k))).map
      (.mk (ULift.up (0 : Fin (n + 2)))) (.mk (ULift.up t.val)) ≫
    eqToHom (congrArg₂ (fun a b : ULift.{u} (Fin (n + 3)) => nerve (SimplicialThickening.Path a b))
      (ULift.ext (source_zero k)) rfl)) ≫ leftMap f hi₀ hiₙ (middle k t) = _
  exact (Category.assoc _ _ _).trans (HornShortFaceRestrictions.left f hi₀ hiₙ k t hk)

/-- The entire right leg reads the same actual supplied face functor with its last endpoint retained. -/
theorem right_readback : MixedFaceProjections.rightLeg k t ≫ rightMap f hi₀ hiₙ (middle k t) =
    retargetMap (HornFaces.faceFunctor f (HornBoxFaces.vertex k) hk)
      (.mk (ULift.up t.val)) (.mk (ULift.up (Fin.last (n + 1))))
      (HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _)
      ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans (congrArg (HornFaces.object f)
        (target_last k))) := by
  change ((coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex k))).map
      (.mk (ULift.up t.val)) (.mk (ULift.up (Fin.last (n + 1)))) ≫
    eqToHom (congrArg₂ (fun a b : ULift.{u} (Fin (n + 3)) => nerve (SimplicialThickening.Path a b))
      rfl (ULift.ext (target_last k)))) ≫ rightMap f hi₀ hiₙ (middle k t) = _
  exact (Category.assoc _ _ _).trans (HornShortFaceRestrictions.right f hi₀ hiₙ k t hk)

/-- The constructed positive and supplied negative maps agree on the entire actual original mixed face. -/
theorem agreement : MixedFaceChart.negativeProjection k t ≫ negativeMap f k hk =
    MixedFaceChart.positiveProjection k t ≫ positiveMap f hi₀ hiₙ (middle k t) := by
  let P := CompositionFace.composition (ULift.up.{u} (0 : Fin (n + 2))) (ULift.up.{u} t.val)
    (ULift.up.{u} (Fin.last (n + 1)))
  let N := retargetMap (HornFaces.faceFunctor f (HornBoxFaces.vertex k) hk)
    (.mk (ULift.up (0 : Fin (n + 2)))) (.mk (ULift.up (Fin.last (n + 1))))
    ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans (congrArg (HornFaces.object f) (source_zero k)))
    ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans (congrArg (HornFaces.object f) (target_last k)))
  let L := leftMap f hi₀ hiₙ (middle k t)
  let R := rightMap f hi₀ hiₙ (middle k t)
  let G := eComp SSet.{u} (HornFaces.object f 0) (HornFaces.object f (HornBoxFaces.vertex (middle k t)))
    (HornFaces.object f (Fin.last (n + 2)))
  apply (cancel_epi (MixedFaceChart.chart k t).hom).mp
  have hN : (MixedFaceChart.chart k t).hom ≫ (MixedFaceChart.negativeProjection k t ≫ negativeMap f k hk) = P ≫ N := by
    rw [← Category.assoc, MixedFaceChart.negative_chart, Category.assoc, HornBoxFaces.negativeMap_readback]
  have hP : (MixedFaceChart.chart k t).hom ≫
      (MixedFaceChart.positiveProjection k t ≫ positiveMap f hi₀ hiₙ (middle k t)) =
      (MixedFaceProjections.leftLeg k t ⊗ₘ MixedFaceProjections.rightLeg k t) ≫ (L ⊗ₘ R) ≫ G := by
    rw [← Category.assoc, MixedFaceProjections.positive_chart, Category.assoc, positiveMap_readback]
  have hT := tensorHom_comp_tensorHom (MixedFaceProjections.leftLeg k t) (MixedFaceProjections.rightLeg k t) L R
  have hTR : ((MixedFaceProjections.leftLeg k t ⊗ₘ MixedFaceProjections.rightLeg k t) ≫ (L ⊗ₘ R)) ≫ G = P ≫ N :=
    (congrArg (fun g => g ≫ G) hT).trans
      ((congrArg (fun g => g ≫ G) (congrArg₂ (fun l r => l ⊗ₘ r)
        (left_readback f hi₀ hiₙ k t hk) (right_readback f hi₀ hiₙ k t hk))).trans
          (HornMapAlgebra.retargetMap_comp (HornFaces.faceFunctor f (HornBoxFaces.vertex k) hk)
            (.mk (ULift.up (0 : Fin (n + 2)))) (.mk (ULift.up t.val)) (.mk (ULift.up (Fin.last (n + 1))))
            ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans (congrArg (HornFaces.object f)
              (source_zero k)))
            (HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _)
            ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans (congrArg (HornFaces.object f)
              (target_last k)))).symm)
  have hPN : (MixedFaceChart.chart k t).hom ≫
      (MixedFaceChart.positiveProjection k t ≫ positiveMap f hi₀ hiₙ (middle k t)) = P ≫ N :=
    hP.trans ((Category.assoc _ _ _).symm.trans hTR)
  exact hN.trans hPN.symm

end CategoryTheory.CoherentRealization.HornMixedOverlap
