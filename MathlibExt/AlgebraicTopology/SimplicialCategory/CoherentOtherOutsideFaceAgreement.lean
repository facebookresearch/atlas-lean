/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentOutsideFaceAgreement

/-!
# Actual agreement through the other original outside horn face

The other supplied face gives the same entire common original interval
map. Its actual coherent operator and both endpoint transports are
retained. Consequently both direct outside-face extractions agree by
the actual horn's common-face relation, without compatibility data or an
assumed enriched-filler outcome.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OtherOutsideFaceAgreement
open SimplicialEnrichment HornHomFaces

private theorem retargetMap_trans {A B : Carrier.{u}} (F : A ⟶ B) (a b : A)
    {x y x' y' : B} (ha : F.obj a = x) (hb : F.obj b = y) (hx : x = x') (hy : y = y') :
    retargetMap F a b ha hb ≫ eqToHom (congrArg₂ (fun x y : B => x ⟶[SSet.{u}] y) hx hy) =
      retargetMap F a b (ha.trans hx) (hb.trans hy) := by
  subst x
  subst y
  subst x'
  subst y'
  change (F.map a b ≫ 𝟙 _) ≫ 𝟙 _ = F.map a b ≫ 𝟙 _
  exact Category.comp_id _

variable {C : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (j k : Fin (n + 3)) (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k)
  (a b : ULift.{u} (Fin (n + 1)))
  (houtj : (ULift.up j : ULift.{u} (Fin (n + 3))) < TwoOutsideFaces.point j k hjk a ∨
    TwoOutsideFaces.point j k hjk b < ULift.up j)
  (houtk : (ULift.up k : ULift.{u} (Fin (n + 3))) < TwoOutsideFaces.point j k hjk a ∨
    TwoOutsideFaces.point j k hjk b < ULift.up k)

include houtk in
/-- The original outside-vertex inequality is unchanged when read through the other common ordinal face. -/
theorem rightOutside :
    (ULift.up k : ULift.{u} (Fin (n + 3))) <
        (OrdinalFace.embedding k) ((OrdinalFace.embedding (j.castPred (Fin.ne_last_of_lt hjk))) a) ∨
      (OrdinalFace.embedding k) ((OrdinalFace.embedding (j.castPred (Fin.ne_last_of_lt hjk))) b) < ULift.up k := by
  rcases houtk with h | h
  · left
    exact (congrArg (fun x => (ULift.up k : ULift.{u} (Fin (n + 3))) < x)
      (TwoOutsideFaces.point_right j k hjk a)).mp h
  · right
    exact (congrArg (fun x => x < (ULift.up k : ULift.{u} (Fin (n + 3))))
      (TwoOutsideFaces.point_right j k hjk b)).mp h

/-- Direct extraction from the other supplied outside face is the same whole original common interval map. -/
theorem right_agreement :
    HornOutsideIntervals.faceMap f k hk
      ((OrdinalFace.embedding (j.castPred (Fin.ne_last_of_lt hjk))) a)
      ((OrdinalFace.embedding (j.castPred (Fin.ne_last_of_lt hjk))) b)
      (rightOutside j k hjk a b houtk)
      (a := (TwoOutsideFaces.point j k hjk a).down)
      (b := (TwoOutsideFaces.point j k hjk b).down)
      (common_vertex j k hjk a.down).symm (common_vertex j k hjk b.down).symm =
        CommonIntervalMaps.rightMap f j k hk hjk a b houtj houtk := by
  let d := coherentSimplexMap (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk)))
  let a' := (OrdinalFace.embedding (j.castPred (Fin.ne_last_of_lt hjk))) a
  let b' := (OrdinalFace.embedding (j.castPred (Fin.ne_last_of_lt hjk))) b
  let E := TwoOutsideFaces.homIso j k hjk a b houtj houtk
  let O := IntervalFaceCover.outsideIso k a' b' (rightOutside j k hjk a b houtk)
  let G := HornOutsideIntervals.faceMap f k hk a' b' (rightOutside j k hjk a b houtk)
    (a := (TwoOutsideFaces.point j k hjk a).down) (b := (TwoOutsideFaces.point j k hjk b).down)
    (common_vertex j k hjk a.down).symm (common_vertex j k hjk b.down).symm
  let S := eqToHom (congrArg₂ (fun a b : Fin (n + 3) =>
    nerve (SimplicialThickening.Path (ULift.up.{u} a) (ULift.up.{u} b)))
      (common_vertex j k hjk a.down).symm (common_vertex j k hjk b.down).symm)
  let T := eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y)
    (congrArg (HornFaces.object f) (common_vertex j k hjk a.down).symm)
    (congrArg (HornFaces.object f) (common_vertex j k hjk b.down).symm))
  let M := HornHomFaces.faceMap f k hk (.mk a') (.mk b')
  let N := retargetMap (d ≫ HornFaces.faceFunctor f k hk) (.mk a) (.mk b)
    ((HornFaces.faceFunctor_obj f k hk (.mk a')).trans
      (congrArg (HornFaces.object f) (common_vertex j k hjk a.down).symm))
    ((HornFaces.faceFunctor_obj f k hk (.mk b')).trans
      (congrArg (HornFaces.object f) (common_vertex j k hjk b.down).symm))
  apply (cancel_epi E.hom).mp
  change E.hom ≫ G = E.hom ≫ CommonIntervalMaps.rightMap f j k hk hjk a b houtj houtk
  have hI : E.hom = (d.map (.mk a) (.mk b) ≫ O.hom) ≫ S := by
    have h₁ := TwoOutsideFaces.homIso_operator j k hjk a b houtj houtk
    have h₂ := CommonIntervalMaps.operator_eq j k hjk a b
    have h₃ := IntervalFaceCover.outsideIso_operator k a' b' (rightOutside j k hjk a b houtk)
    exact h₁.trans (h₂.symm.trans (congrArg (fun t => (d.map (.mk a) (.mk b) ≫ t) ≫ S) h₃.symm))
  have hG : O.hom ≫ (S ≫ G) = M ≫ T :=
    HornOutsideIntervals.faceMap_readback f k hk a' b' (rightOutside j k hjk a b houtk)
      (common_vertex j k hjk a.down).symm (common_vertex j k hjk b.down).symm
  have hM : d.map (.mk a) (.mk b) ≫ (M ≫ T) = N := by
    have h₁ := retargetMap_trans (HornFaces.faceFunctor f k hk) (.mk a') (.mk b')
      (HornFaces.faceFunctor_obj f k hk (.mk a')) (HornFaces.faceFunctor_obj f k hk (.mk b'))
      (congrArg (HornFaces.object f) (common_vertex j k hjk a.down).symm)
      (congrArg (HornFaces.object f) (common_vertex j k hjk b.down).symm)
    have h₂ := HornMapAlgebra.retargetMap_precomp d (HornFaces.faceFunctor f k hk) (.mk a) (.mk b)
      ((HornFaces.faceFunctor_obj f k hk (.mk a')).trans
        (congrArg (HornFaces.object f) (common_vertex j k hjk a.down).symm))
      ((HornFaces.faceFunctor_obj f k hk (.mk b')).trans
        (congrArg (HornFaces.object f) (common_vertex j k hjk b.down).symm))
    exact (congrArg (fun t => d.map (.mk a) (.mk b) ≫ t) h₁).trans h₂
  have hA : ((d.map (.mk a) (.mk b) ≫ O.hom) ≫ S) ≫ G =
      d.map (.mk a) (.mk b) ≫ (O.hom ≫ (S ≫ G)) :=
    (congrArg (fun t => t ≫ G) (Category.assoc (d.map (.mk a) (.mk b)) O.hom S)).trans
      ((Category.assoc (d.map (.mk a) (.mk b)) (O.hom ≫ S) G).trans
        (congrArg (fun t => d.map (.mk a) (.mk b) ≫ t) (Category.assoc O.hom S G)))
  have hL : E.hom ≫ G = N :=
    (congrArg (fun t => t ≫ G) hI).trans
      (hA.trans ((congrArg (fun t => d.map (.mk a) (.mk b) ≫ t) hG).trans hM))
  exact hL.trans (CommonIntervalMaps.rightMap_readback f j k hk hjk a b houtj houtk).symm

end CategoryTheory.CoherentRealization.OtherOutsideFaceAgreement
