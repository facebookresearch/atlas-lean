/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentTwoOutsideFaces
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornMapAlgebra

/-!
# The actual common whole Hom map of two supplied outside horn faces

Two available original outside faces induce the same entire Hom map on
the common original endpoint interval. The maps are obtained from their
actual enriched face functors through the proved whole Hom isomorphism.
Their agreement is proved from the supplied horn map. Both source
operators and all endpoint transports are stated literally.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.CommonIntervalMaps
open SimplicialEnrichment HornHomFaces
/-- The actual other common-face operator reads back the same whole original Hom after its precise endpoint
  transport. -/
theorem operator_eq {n : ℕ} (j k : Fin (n + 3)) (hjk : j < k)
    (a b : ULift.{u} (Fin (n + 1))) :
    (coherentSimplexMap (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk))) ≫
      coherentSimplexMap (SimplexCategory.δ k)).map (.mk a) (.mk b) ≫
        eqToHom (congrArg₂ (fun x y : ULift.{u} (Fin (n + 3)) => nerve (SimplicialThickening.Path x y))
          (TwoOutsideFaces.point_right j k hjk a).symm (TwoOutsideFaces.point_right j k hjk b).symm) =
      (coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk))) ≫
        coherentSimplexMap (SimplexCategory.δ j)).map (.mk a) (.mk b) := by
  have hδ : SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ SimplexCategory.δ k =
      SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ SimplexCategory.δ j := by
    apply SimplexCategory.δ_comp_δ'
    simpa only [Fin.castSucc_castPred] using hjk
  have hF : coherentSimplexMap (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk))) ≫
      coherentSimplexMap (SimplexCategory.δ k) =
        coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk))) ≫
          coherentSimplexMap (SimplexCategory.δ j) :=
    (coherentSimplices.map_comp _ _).symm.trans
      ((congrArg (fun θ : ⦋n⦌ ⟶ ⦋n + 2⦌ => coherentSimplexMap θ) hδ).trans
        (coherentSimplices.map_comp _ _))
  exact enriched_map_of_eq hF (.mk a) (.mk b)

variable {C : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (j k : Fin (n + 3)) (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k)
  (a b : ULift.{u} (Fin (n + 1)))
  (houtj : (ULift.up j : ULift.{u} (Fin (n + 3))) < TwoOutsideFaces.point j k hjk a ∨
    TwoOutsideFaces.point j k hjk b < ULift.up j)
  (houtk : (ULift.up k : ULift.{u} (Fin (n + 3))) < TwoOutsideFaces.point j k hjk a ∨
    TwoOutsideFaces.point j k hjk b < ULift.up k)

/-- The common original Hom map extracted through the first supplied outside face. -/
def leftMap :
    nerve (SimplicialThickening.Path (TwoOutsideFaces.point j k hjk a) (TwoOutsideFaces.point j k hjk b)) ⟶
      (HornFaces.object f (TwoOutsideFaces.point j k hjk a).down ⟶[SSet.{u}]
        HornFaces.object f (TwoOutsideFaces.point j k hjk b).down) :=
  (TwoOutsideFaces.homIso j k hjk a b houtj houtk).inv ≫
    retargetMap
      (coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk))) ≫ HornFaces.faceFunctor f j hj)
      (.mk a) (.mk b)
      (HornFaces.faceFunctor_obj f j hj
        ((coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk)))).obj (.mk a)))
      (HornFaces.faceFunctor_obj f j hj
        ((coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk)))).obj (.mk b)))

/-- The same whole original Hom map extracted through the other actual supplied outside face. -/
def rightMap :
    nerve (SimplicialThickening.Path (TwoOutsideFaces.point j k hjk a) (TwoOutsideFaces.point j k hjk b)) ⟶
      (HornFaces.object f (TwoOutsideFaces.point j k hjk a).down ⟶[SSet.{u}]
        HornFaces.object f (TwoOutsideFaces.point j k hjk b).down) :=
  (TwoOutsideFaces.homIso j k hjk a b houtj houtk).inv ≫
    retargetMap
      (coherentSimplexMap (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk))) ≫ HornFaces.faceFunctor f k hk)
      (.mk a) (.mk b)
      ((HornFaces.faceFunctor_obj f k hk
        ((coherentSimplexMap (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk)))).obj (.mk a))).trans
          (congrArg (HornFaces.object f) (common_vertex j k hjk a.down).symm))
      ((HornFaces.faceFunctor_obj f k hk
        ((coherentSimplexMap (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk)))).obj (.mk b))).trans
          (congrArg (HornFaces.object f) (common_vertex j k hjk b.down).symm))

/-- Both actual outside-face extractions give exactly the same whole Hom map, using their proved original
  horn agreement. -/
theorem leftMap_eq_rightMap : leftMap f j k hj hjk a b houtj houtk = rightMap f j k hk hjk a b houtj houtk :=
  congrArg (fun g => (TwoOutsideFaces.homIso j k hjk a b houtj houtk).inv ≫ g)
    (common_map f j k hj hk hjk (.mk a) (.mk b))

/-- Reading the first extraction along the actual common-face operator recovers its entire actual face Hom map. -/
theorem leftMap_readback :
    (TwoOutsideFaces.homIso j k hjk a b houtj houtk).hom ≫ leftMap f j k hj hjk a b houtj houtk =
      retargetMap
        (coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk))) ≫ HornFaces.faceFunctor f j hj)
        (.mk a) (.mk b)
        (HornFaces.faceFunctor_obj f j hj
          ((coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk)))).obj (.mk a)))
        (HornFaces.faceFunctor_obj f j hj
          ((coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk)))).obj (.mk b))) := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ _) (TwoOutsideFaces.homIso j k hjk a b houtj houtk).hom_inv_id).trans
      (Category.id_comp _))

/-- Reading the other extraction recovers its entire actual face Hom map at precisely the same original endpoints. -/
theorem rightMap_readback :
    (TwoOutsideFaces.homIso j k hjk a b houtj houtk).hom ≫ rightMap f j k hk hjk a b houtj houtk =
      retargetMap
        (coherentSimplexMap (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk))) ≫ HornFaces.faceFunctor f k hk)
        (.mk a) (.mk b)
        ((HornFaces.faceFunctor_obj f k hk
          ((coherentSimplexMap (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk)))).obj (.mk a))).trans
            (congrArg (HornFaces.object f) (common_vertex j k hjk a.down).symm))
        ((HornFaces.faceFunctor_obj f k hk
          ((coherentSimplexMap (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk)))).obj (.mk b))).trans
            (congrArg (HornFaces.object f) (common_vertex j k hjk b.down).symm)) := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ _) (TwoOutsideFaces.homIso j k hjk a b houtj houtk).hom_inv_id).trans
      (Category.id_comp _))

end CategoryTheory.CoherentRealization.CommonIntervalMaps
