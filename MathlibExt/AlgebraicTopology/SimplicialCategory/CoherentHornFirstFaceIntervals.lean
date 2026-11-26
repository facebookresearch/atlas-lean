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
# Whole original interval restrictions of the supplied first endpoint face

Every original face preserving zero carries the first-face Hom map on
its positive source intervals. The actual common-face restriction and
its original interval preimages give the entire supplied face Hom map.
-/

noncomputable section
universe u
open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HornFirstFaceIntervals
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
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C) (hi₀ : i ≠ 0)

/-- The actual supplied first-face whole Hom map restricts to every other face preserving zero, at all
  original positive interval endpoints. -/
theorem restriction (k : Fin (n + 3)) (hk₀ : k ≠ 0) (hk : k ≠ i)
    (a b : Fin (n + 2)) (ha : a ≠ 0) (hb : b ≠ 0) :
    (coherentSimplexMap (SimplexCategory.δ k)).map (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) ≫
      HornOrderedMaps.firstMap f hi₀ (k.succAbove a) (k.succAbove b)
        (HornIntervalPreimages.image_ne_zero k hk₀ a ha) (HornIntervalPreimages.image_ne_zero k hk₀ b hb) =
        HornHomFaces.faceMap f k hk (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) := by
  let E := coherentSimplexMap (SimplexCategory.δ k)
  let F := HornFaces.faceFunctor f k hk
  let d := coherentSimplexMap (SimplexCategory.δ (0 : Fin (n + 2)))
  let a' : ULift.{u} (Fin (n + 1)) := ULift.up (a.pred ha)
  let b' : ULift.{u} (Fin (n + 1)) := ULift.up (b.pred hb)
  let h₀k := Fin.pos_iff_ne_zero.mpr hk₀
  let hA := congrArg ULift.down (HornIntervalPreimages.first_point.{u} k hk₀ a ha)
  let hB := congrArg ULift.down (HornIntervalPreimages.first_point.{u} k hk₀ b hb)
  have h := EndpointRestrictionRetarget.first f hi₀.symm k h₀k a' b' hk
    (a := k.succAbove a) (b := k.succAbove b) hA hB
  have hpA := HornIntervalPreimages.first_preimage.{u} k hk₀ a ha
  have hpB := HornIntervalPreimages.first_preimage.{u} k hk₀ b hb
  have hdA : d.obj (.mk a') = (.mk (ULift.up.{u} a) : coherentSimplex.{u} ⦋n + 1⦌) := by
    change SimplicialThickening.mk ((OrdinalFace.embedding (0 : Fin (n + 2))) a') = _
    apply congrArg SimplicialThickening.mk
    apply ULift.ext
    change (a.pred ha).succ = a
    exact Fin.succ_pred a ha
  have hdB : d.obj (.mk b') = (.mk (ULift.up.{u} b) : coherentSimplex.{u} ⦋n + 1⦌) := by
    change SimplicialThickening.mk ((OrdinalFace.embedding (0 : Fin (n + 2))) b') = _
    apply congrArg SimplicialThickening.mk
    apply ULift.ext
    change (b.pred hb).succ = b
    exact Fin.succ_pred b hb
  let M := HornOutsideIntervals.faceMap f (0 : Fin (n + 3)) hi₀.symm
    ((OrdinalFace.embedding (k.pred hk₀)) a') ((OrdinalFace.embedding (k.pred hk₀)) b')
    (FirstFaceRestriction.outside k h₀k a' b') hA hB
  have hM : M = HornOrderedMaps.firstMap f hi₀ (k.succAbove a) (k.succAbove b)
      (HornIntervalPreimages.image_ne_zero k hk₀ a ha) (HornIntervalPreimages.image_ne_zero k hk₀ b hb) := by
    exact OutsideFaceMapCongruence.source_eq f 0 hi₀.symm
      ((OrdinalFace.embedding (k.pred hk₀)) a') ((OrdinalFace.embedding (k.pred hk₀)) b')
      (ULift.up ((k.succAbove a).pred (HornIntervalPreimages.image_ne_zero k hk₀ a ha)))
      (ULift.up ((k.succAbove b).pred (HornIntervalPreimages.image_ne_zero k hk₀ b hb))) hpA hpB
      (FirstFaceRestriction.outside k h₀k a' b')
      (Or.inl (show (ULift.up (0 : Fin (n + 3)) : ULift.{u} (Fin (n + 3))) <
        (OrdinalFace.embedding 0) (ULift.up ((k.succAbove a).pred (HornIntervalPreimages.image_ne_zero k hk₀
          a ha))) from by
          change (0 : Fin (n + 3)) < (0 : Fin (n + 3)).succAbove ((k.succAbove a).pred
            (HornIntervalPreimages.image_ne_zero k hk₀ a ha))
          simpa only [Fin.succAbove_zero, Fin.succ_pred] using Fin.pos_iff_ne_zero.mpr
            (HornIntervalPreimages.image_ne_zero k hk₀ a ha)))
      hA hB (Fin.succ_pred (k.succAbove a) (HornIntervalPreimages.image_ne_zero k hk₀ a ha))
      (Fin.succ_pred (k.succAbove b) (HornIntervalPreimages.image_ne_zero k hk₀ b hb))
  let hx := (TwoOutsideFaces.point_right 0 k h₀k a').symm.trans (ULift.ext hA)
  let hy := (TwoOutsideFaces.point_right 0 k h₀k b').symm.trans (ULift.ext hB)
  have h' : E.map (d.obj (.mk a')) (d.obj (.mk b')) ≫
      eqToHom (congrArg₂ (fun a b : coherentSimplex.{u} ⦋n + 2⦌ => a ⟶[SSet.{u}] b)
        (congrArg SimplicialThickening.mk hx) (congrArg SimplicialThickening.mk hy)) ≫ M =
      retargetMap F (d.obj (.mk a')) (d.obj (.mk b'))
        ((HornFaces.faceFunctor_obj f k hk _).trans (congrArg (HornFaces.object f) ((common_vertex 0 k h₀k
          a'.down).symm.trans hA)))
        ((HornFaces.faceFunctor_obj f k hk _).trans (congrArg (HornFaces.object f) ((common_vertex 0 k h₀k
          b'.down).symm.trans hB))) := h
  have hFinal := reindex_source E F hdA hdB M
    (congrArg SimplicialThickening.mk hx) (congrArg SimplicialThickening.mk hy)
    ((HornFaces.faceFunctor_obj f k hk _).trans (congrArg (HornFaces.object f) ((common_vertex 0 k h₀k
      a'.down).symm.trans hA)))
    ((HornFaces.faceFunctor_obj f k hk _).trans (congrArg (HornFaces.object f) ((common_vertex 0 k h₀k
      b'.down).symm.trans hB)))
    rfl rfl (HornFaces.faceFunctor_obj f k hk _) (HornFaces.faceFunctor_obj f k hk _) h'
  change E.map (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) ≫ 𝟙 _ ≫ M =
    HornHomFaces.faceMap f k hk (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) at hFinal
  have hN : E.map (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) ≫ M =
      HornHomFaces.faceMap f k hk (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) :=
    (congrArg (fun g => E.map (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) ≫ g) (Category.id_comp M)).symm.trans hFinal
  exact (congrArg (fun g => E.map (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) ≫ g) hM).symm.trans hN

end CategoryTheory.CoherentRealization.HornFirstFaceIntervals
