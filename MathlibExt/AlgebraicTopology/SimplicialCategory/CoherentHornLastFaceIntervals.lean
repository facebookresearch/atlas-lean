/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornIntervalPreimages
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornOrderedMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornEndpointRestrictionRetarget
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentOutsideFaceMapCongruence

/-!
# Whole original interval restrictions of the supplied last endpoint face

Every original face preserving the last endpoint carries its actual last-
face Hom map on intervals before that endpoint. The genuine common-face
restriction retains each original vertex and the entire supplied Hom map.
-/

noncomputable section
universe u
open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HornLastFaceIntervals
open SimplicialEnrichment HornHomFaces

private theorem reindex_source {A B C : Carrier.{u}} (E : A ⟶ B) (F : A ⟶ C)
    {a b a' b' : A} (ha : a = a') (hb : b = b') {x y : B} {z w : C}
    (M : (x ⟶[SSet.{u}] y) ⟶ (z ⟶[SSet.{u}] w))
    (hx : E.obj a = x) (hy : E.obj b = y) (hz : F.obj a = z) (hw : F.obj b = w)
    (hx' : E.obj a' = x) (hy' : E.obj b' = y) (hz' : F.obj a' = z) (hw' : F.obj b' = w)
    (h : E.map a b ≫ eqToHom (congrArg₂ (fun x y : B => x ⟶[SSet.{u}] y) hx hy) ≫ M = retargetMap F a b hz hw) :
    E.map a' b' ≫ eqToHom (congrArg₂ (fun x y : B => x ⟶[SSet.{u}] y) hx' hy') ≫ M = retargetMap F a' b' hz' hw' := by
  subst a'
  subst b'
  exact h

variable {C : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C) (hiₙ : i ≠ Fin.last (n + 2))

/-- The actual last-face whole Hom map restricts to every other face preserving the last endpoint, at all
  original interval vertices before it. -/
theorem restriction (k : Fin (n + 3)) (hkₙ : k ≠ Fin.last (n + 2)) (hk : k ≠ i)
    (a b : Fin (n + 2)) (ha : a ≠ Fin.last (n + 1)) (hb : b ≠ Fin.last (n + 1)) :
    (coherentSimplexMap (SimplexCategory.δ k)).map (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) ≫
      HornOrderedMaps.lastMap f hiₙ (k.succAbove a) (k.succAbove b)
        (HornIntervalPreimages.image_ne_last k hkₙ a ha) (HornIntervalPreimages.image_ne_last k hkₙ b hb) =
        HornHomFaces.faceMap f k hk (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) := by
  let E := coherentSimplexMap (SimplexCategory.δ k)
  let F := HornFaces.faceFunctor f k hk
  let d := coherentSimplexMap (SimplexCategory.δ (Fin.last (n + 1)))
  let a' : ULift.{u} (Fin (n + 1)) := ULift.up (a.castPred ha)
  let b' : ULift.{u} (Fin (n + 1)) := ULift.up (b.castPred hb)
  let hkLast := Fin.lt_last_iff_ne_last.mpr hkₙ
  let hA := congrArg ULift.down (HornIntervalPreimages.last_point.{u} k hkₙ a ha)
  let hB := congrArg ULift.down (HornIntervalPreimages.last_point.{u} k hkₙ b hb)
  have h := EndpointRestrictionRetarget.last f hiₙ.symm k hkLast a' b' hk
    (a := k.succAbove a) (b := k.succAbove b) hA hB
  have hpA := HornIntervalPreimages.last_preimage.{u} k hkₙ a ha
  have hpB := HornIntervalPreimages.last_preimage.{u} k hkₙ b hb
  have hdA : d.obj (.mk a') = (.mk (ULift.up.{u} a) : coherentSimplex.{u} ⦋n + 1⦌) := by
    change SimplicialThickening.mk ((OrdinalFace.embedding (Fin.last (n + 1))) a') = _
    apply congrArg SimplicialThickening.mk
    apply ULift.ext
    change (Fin.last (n + 1)).succAbove (a.castPred ha) = a
    simpa only [Fin.succAbove_last] using Fin.castSucc_castPred a ha
  have hdB : d.obj (.mk b') = (.mk (ULift.up.{u} b) : coherentSimplex.{u} ⦋n + 1⦌) := by
    change SimplicialThickening.mk ((OrdinalFace.embedding (Fin.last (n + 1))) b') = _
    apply congrArg SimplicialThickening.mk
    apply ULift.ext
    change (Fin.last (n + 1)).succAbove (b.castPred hb) = b
    simpa only [Fin.succAbove_last] using Fin.castSucc_castPred b hb
  let M := HornOutsideIntervals.faceMap f (Fin.last (n + 2)) hiₙ.symm
    ((OrdinalFace.embedding (k.castPred hkₙ)) a') ((OrdinalFace.embedding (k.castPred hkₙ)) b')
    (LastFaceRestriction.outside k hkLast a' b')
    ((common_vertex k (Fin.last (n + 2)) hkLast a'.down).symm.trans hA)
    ((common_vertex k (Fin.last (n + 2)) hkLast b'.down).symm.trans hB)
  have hM : M = HornOrderedMaps.lastMap f hiₙ (k.succAbove a) (k.succAbove b)
      (HornIntervalPreimages.image_ne_last k hkₙ a ha) (HornIntervalPreimages.image_ne_last k hkₙ b hb) := by
    exact OutsideFaceMapCongruence.source_eq f (Fin.last (n + 2)) hiₙ.symm
      ((OrdinalFace.embedding (k.castPred hkₙ)) a') ((OrdinalFace.embedding (k.castPred hkₙ)) b')
      (ULift.up ((k.succAbove a).castPred (HornIntervalPreimages.image_ne_last k hkₙ a ha)))
      (ULift.up ((k.succAbove b).castPred (HornIntervalPreimages.image_ne_last k hkₙ b hb))) hpA hpB
      (LastFaceRestriction.outside k hkLast a' b')
      (Or.inr (show (OrdinalFace.embedding (Fin.last (n + 2)))
        (ULift.up ((k.succAbove b).castPred (HornIntervalPreimages.image_ne_last k hkₙ b hb))) <
          (ULift.up (Fin.last (n + 2)) : ULift.{u} (Fin (n + 3))) from by
            change (Fin.last (n + 2)).succAbove ((k.succAbove b).castPred
              (HornIntervalPreimages.image_ne_last k hkₙ b hb)) < Fin.last (n + 2)
            simpa only [Fin.succAbove_last, Fin.castSucc_castPred] using Fin.lt_last_iff_ne_last.mpr
              (HornIntervalPreimages.image_ne_last k hkₙ b hb)))
      ((common_vertex k (Fin.last (n + 2)) hkLast a'.down).symm.trans hA)
      ((common_vertex k (Fin.last (n + 2)) hkLast b'.down).symm.trans hB)
      (by
        change (Fin.last (n + 2)).succAbove ((k.succAbove a).castPred (HornIntervalPreimages.image_ne_last k
          hkₙ a ha)) = k.succAbove a
        simpa only [Fin.succAbove_last] using Fin.castSucc_castPred (k.succAbove a)
          (HornIntervalPreimages.image_ne_last k hkₙ a ha))
      (by
        change (Fin.last (n + 2)).succAbove ((k.succAbove b).castPred (HornIntervalPreimages.image_ne_last k
          hkₙ b hb)) = k.succAbove b
        simpa only [Fin.succAbove_last] using Fin.castSucc_castPred (k.succAbove b)
          (HornIntervalPreimages.image_ne_last k hkₙ b hb))
  have h' : E.map (d.obj (.mk a')) (d.obj (.mk b')) ≫
      eqToHom (congrArg₂ (fun a b : coherentSimplex.{u} ⦋n + 2⦌ => a ⟶[SSet.{u}] b)
        (congrArg (fun a : Fin (n + 3) => SimplicialThickening.mk (ULift.up.{u} a)) hA)
        (congrArg (fun b : Fin (n + 3) => SimplicialThickening.mk (ULift.up.{u} b)) hB)) ≫ M =
      retargetMap F (d.obj (.mk a')) (d.obj (.mk b'))
        ((HornFaces.faceFunctor_obj f k hk _).trans (congrArg (HornFaces.object f) hA))
        ((HornFaces.faceFunctor_obj f k hk _).trans (congrArg (HornFaces.object f) hB)) := h
  have hFinal := reindex_source E F hdA hdB M
    (congrArg (fun a : Fin (n + 3) => SimplicialThickening.mk (ULift.up.{u} a)) hA)
    (congrArg (fun b : Fin (n + 3) => SimplicialThickening.mk (ULift.up.{u} b)) hB)
    ((HornFaces.faceFunctor_obj f k hk _).trans (congrArg (HornFaces.object f) hA))
    ((HornFaces.faceFunctor_obj f k hk _).trans (congrArg (HornFaces.object f) hB))
    rfl rfl (HornFaces.faceFunctor_obj f k hk _) (HornFaces.faceFunctor_obj f k hk _) h'
  change E.map (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) ≫ 𝟙 _ ≫ M =
    HornHomFaces.faceMap f k hk (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) at hFinal
  have hN : E.map (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) ≫ M =
      HornHomFaces.faceMap f k hk (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) :=
    (congrArg (fun g => E.map (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) ≫ g) (Category.id_comp M)).symm.trans hFinal
  exact (congrArg (fun g => E.map (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) ≫ g) hM).symm.trans hN

end CategoryTheory.CoherentRealization.HornLastFaceIntervals
