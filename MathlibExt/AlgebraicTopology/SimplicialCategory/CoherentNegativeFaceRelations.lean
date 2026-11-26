/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentDoubleOrdinalFace

/-!
# Actual common negative-face Hom relations of a supplied coherent horn

Both supplied negative-face maps agree after restriction through their
actual common coherent Hom chart. The chart is the original double
ordinal face, and both endpoint equality transports remain explicit.
The equality follows from the actual horn map's face relation, including
when both omitted vertices lie inside the outer endpoint interval.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.NegativeFaceRelations
open SimplicialEnrichment HornHomFaces

private theorem post_retarget {A B : Carrier.{u}} (F : A ⟶ B) (a b : A)
    {x y x' y' : B} (ha : F.obj a = x) (hb : F.obj b = y) (hx : x = x') (hy : y = y') :
    retargetMap F a b ha hb ≫ eqToHom (congrArg₂ (fun x y : B => x ⟶[SSet.{u}] y) hx hy) =
      retargetMap F a b (ha.trans hx) (hb.trans hy) := by
  rw [retargetMap, retargetMap, Category.assoc, eqToHom_trans]

variable {C : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (j k : Fin (n + 3)) (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k)
  (a b : ULift.{u} (Fin (n + 1)))

/-- The actual first negative-face Hom map on its original common ordinal Hom chart. -/
def leftRestriction : nerve (SimplicialThickening.Path a b) ⟶
    (HornFaces.object f (TwoOutsideFaces.point j k hjk a).down ⟶[SSet.{u}]
      HornFaces.object f (TwoOutsideFaces.point j k hjk b).down) :=
  (coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk)))).map (.mk a) (.mk b) ≫
    (OrdinalFace.negativeIso j ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) a)
      ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) b)).hom ≫
        negativeMap f j hj ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) a)
          ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) b)

/-- The actual other negative-face Hom map on the same original common chart and endpoints. -/
def rightRestriction : nerve (SimplicialThickening.Path a b) ⟶
    (HornFaces.object f (TwoOutsideFaces.point j k hjk a).down ⟶[SSet.{u}]
      HornFaces.object f (TwoOutsideFaces.point j k hjk b).down) :=
  (coherentSimplexMap (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk)))).map (.mk a) (.mk b) ≫
    (OrdinalFace.negativeIso k ((OrdinalFace.embedding (j.castPred (Fin.ne_last_of_lt hjk))) a)
      ((OrdinalFace.embedding (j.castPred (Fin.ne_last_of_lt hjk))) b)).hom ≫
        negativeMap f k hk ((OrdinalFace.embedding (j.castPred (Fin.ne_last_of_lt hjk))) a)
          ((OrdinalFace.embedding (j.castPred (Fin.ne_last_of_lt hjk))) b) ≫
            eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y)
              (congrArg (HornFaces.object f) (common_vertex j k hjk a.down).symm)
              (congrArg (HornFaces.object f) (common_vertex j k hjk b.down).symm))

/-- The first actual restricted negative-face map reads back the entire supplied common face functor's Hom map. -/
theorem left_readback : leftRestriction f j k hj hjk a b =
    retargetMap
      (coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk))) ≫ HornFaces.faceFunctor f j hj)
      (.mk a) (.mk b)
      (HornFaces.faceFunctor_obj f j hj
        ((coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk)))).obj (.mk a)))
      (HornFaces.faceFunctor_obj f j hj
        ((coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk)))).obj (.mk b))) := by
  have h₁ := negativeMap_readback f j hj
    ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) a)
    ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) b)
  have h₂ := HornMapAlgebra.retargetMap_precomp
    (coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk)))) (HornFaces.faceFunctor f j hj)
    (.mk a) (.mk b)
    (HornFaces.faceFunctor_obj f j hj
      ((coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk)))).obj (.mk a)))
    (HornFaces.faceFunctor_obj f j hj
      ((coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk)))).obj (.mk b)))
  exact (congrArg (fun h =>
    (coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk)))).map (.mk a) (.mk b) ≫ h) h₁).trans h₂

/-- The other actual restricted negative-face map reads back its entire supplied common face Hom at the same
  original endpoints. -/
theorem right_readback : rightRestriction f j k hk hjk a b =
    retargetMap
      (coherentSimplexMap (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk))) ≫ HornFaces.faceFunctor f k hk)
      (.mk a) (.mk b)
      ((HornFaces.faceFunctor_obj f k hk
        ((coherentSimplexMap (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk)))).obj (.mk a))).trans
          (congrArg (HornFaces.object f) (common_vertex j k hjk a.down).symm))
      ((HornFaces.faceFunctor_obj f k hk
        ((coherentSimplexMap (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk)))).obj (.mk b))).trans
          (congrArg (HornFaces.object f) (common_vertex j k hjk b.down).symm)) := by
  let d := coherentSimplexMap (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk)))
  let a' := (OrdinalFace.embedding (j.castPred (Fin.ne_last_of_lt hjk))) a
  let b' := (OrdinalFace.embedding (j.castPred (Fin.ne_last_of_lt hjk))) b
  let e := OrdinalFace.negativeIso k a' b'
  let N := negativeMap f k hk a' b'
  let M := HornHomFaces.faceMap f k hk (.mk a') (.mk b')
  let T := eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y)
    (congrArg (HornFaces.object f) (common_vertex j k hjk a.down).symm)
    (congrArg (HornFaces.object f) (common_vertex j k hjk b.down).symm))
  have h₁ : e.hom ≫ (N ≫ T) = M ≫ T :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun h => h ≫ T) (negativeMap_readback f k hk a' b'))
  have h₂ := post_retarget (HornFaces.faceFunctor f k hk) (.mk a') (.mk b')
    (HornFaces.faceFunctor_obj f k hk (.mk a')) (HornFaces.faceFunctor_obj f k hk (.mk b'))
    (congrArg (HornFaces.object f) (common_vertex j k hjk a.down).symm)
    (congrArg (HornFaces.object f) (common_vertex j k hjk b.down).symm)
  have h₃ := HornMapAlgebra.retargetMap_precomp d (HornFaces.faceFunctor f k hk) (.mk a) (.mk b)
    ((HornFaces.faceFunctor_obj f k hk (.mk a')).trans
      (congrArg (HornFaces.object f) (common_vertex j k hjk a.down).symm))
    ((HornFaces.faceFunctor_obj f k hk (.mk b')).trans
      (congrArg (HornFaces.object f) (common_vertex j k hjk b.down).symm))
  exact (congrArg (fun h => d.map (.mk a) (.mk b) ≫ h) h₁).trans
    ((congrArg (fun h => d.map (.mk a) (.mk b) ≫ h) h₂).trans h₃)

/-- The two actual negative-face maps agree on the entire original common coherent Hom chart. -/
theorem restriction_agreement : leftRestriction f j k hj hjk a b = rightRestriction f j k hk hjk a b :=
  (left_readback f j k hj hjk a b).trans
    ((common_map f j k hj hk hjk (.mk a) (.mk b)).trans (right_readback f j k hk hjk a b).symm)

end CategoryTheory.CoherentRealization.NegativeFaceRelations
