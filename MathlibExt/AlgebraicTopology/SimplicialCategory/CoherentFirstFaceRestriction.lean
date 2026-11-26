/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentOutsideNegativeMap

/-!
# The actual first endpoint-face Hom map restricts to supplied faces

The original first endpoint face carries every whole Hom interval whose
source is positive. Its map agrees with the actual supplied face map on
the supported short leg of any other available face. The proof uses the
actual common negative-face relation and the genuine whole Hom isomorphism
of the first ordinal face; no compatibility outcome is assumed.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.FirstFaceRestriction
open SimplicialEnrichment HornHomFaces
variable {C : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C) (h₀ : (0 : Fin (n + 3)) ≠ i)
  (k : Fin (n + 3)) (h₀k : 0 < k) (a b : ULift.{u} (Fin (n + 1)))

/-- The original common interval lies strictly after the omitted first endpoint. -/
theorem outside : (ULift.up (0 : Fin (n + 3)) : ULift.{u} (Fin (n + 3))) < TwoOutsideFaces.point 0 k h₀k a ∨
    TwoOutsideFaces.point 0 k h₀k b < ULift.up 0 := by
  left
  change (0 : Fin (n + 3)) < ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt h₀k))) a).down.succ
  exact Fin.succ_pos _

/-- The actual first endpoint-face map on the same original common interval. -/
def map : nerve (SimplicialThickening.Path (TwoOutsideFaces.point 0 k h₀k a) (TwoOutsideFaces.point 0 k h₀k b)) ⟶
    (HornFaces.object f (TwoOutsideFaces.point 0 k h₀k a).down ⟶[SSet.{u}]
      HornFaces.object f (TwoOutsideFaces.point 0 k h₀k b).down) :=
  HornOutsideIntervals.faceMap f 0 h₀ ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt h₀k))) a)
    ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt h₀k))) b) (outside k h₀k a b) rfl rfl

/-- The actual endpoint-face Hom map restricts to the other supplied face with the same whole original short
  leg and endpoints. -/
theorem restriction (hk : k ≠ i) :
    (coherentSimplexMap (SimplexCategory.δ k)).map
      ((coherentSimplexMap (SimplexCategory.δ (0 : Fin (n + 2)))).obj (.mk a))
      ((coherentSimplexMap (SimplexCategory.δ (0 : Fin (n + 2)))).obj (.mk b)) ≫
        eqToHom (congrArg₂ (fun a b : ULift.{u} (Fin (n + 3)) => nerve (SimplicialThickening.Path a b))
          (TwoOutsideFaces.point_right 0 k h₀k a).symm (TwoOutsideFaces.point_right 0 k h₀k b).symm) ≫
            map f h₀ k h₀k a b =
    HornHomFaces.faceMap f k hk
      ((coherentSimplexMap (SimplexCategory.δ (0 : Fin (n + 2)))).obj (.mk a))
      ((coherentSimplexMap (SimplexCategory.δ (0 : Fin (n + 2)))).obj (.mk b)) ≫
        eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y)
          (congrArg (HornFaces.object f) (common_vertex 0 k h₀k a.down).symm)
          (congrArg (HornFaces.object f) (common_vertex 0 k h₀k b.down).symm)) := by
  let d := coherentSimplexMap (SimplexCategory.δ (0 : Fin (n + 2)))
  let dl := coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt h₀k)))
  let a' := (OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt h₀k))) a
  let b' := (OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt h₀k))) b
  let E := IntervalFaceCover.outsideIso (0 : Fin (n + 2)) a b
    (Or.inl (show (ULift.up (0 : Fin (n + 2)) : ULift.{u} (Fin (n + 2))) < (OrdinalFace.embedding 0) a from
      Fin.succ_pos a.down))
  have hE : E.hom = d.map (.mk a) (.mk b) :=
    IntervalFaceCover.outsideIso_operator (0 : Fin (n + 2)) a b _
  let _ : IsIso (d.map (.mk a) (.mk b)) := hE ▸ E.isIso_hom
  let G := map f h₀ k h₀k a b
  let R := (coherentSimplexMap (SimplexCategory.δ k)).map (d.obj (.mk a)) (d.obj (.mk b))
  let S := eqToHom (congrArg₂ (fun a b : ULift.{u} (Fin (n + 3)) => nerve (SimplicialThickening.Path a b))
    (TwoOutsideFaces.point_right 0 k h₀k a).symm (TwoOutsideFaces.point_right 0 k h₀k b).symm)
  let T := eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y)
    (congrArg (HornFaces.object f) (common_vertex 0 k h₀k a.down).symm)
    (congrArg (HornFaces.object f) (common_vertex 0 k h₀k b.down).symm))
  let M := HornHomFaces.faceMap f k hk (d.obj (.mk a)) (d.obj (.mk b))
  let O := OrdinalFace.negativeIso 0 a' b'
  let N := negativeMap f 0 h₀ a' b'
  apply (cancel_epi (d.map (.mk a) (.mk b))).mp
  have hS : (d.map (.mk a) (.mk b) ≫ R) ≫ S =
      dl.map (.mk a) (.mk b) ≫ (coherentSimplexMap (SimplexCategory.δ (0 : Fin (n + 3)))).map (.mk a') (.mk b') :=
    CommonIntervalMaps.operator_eq 0 k h₀k a b
  have hN : (coherentSimplexMap (SimplexCategory.δ (0 : Fin (n + 3)))).map (.mk a') (.mk b') ≫ G = O.hom ≫ N :=
    (congrArg (fun h => h ≫ G) (OrdinalFace.negativeIso_operator 0 a' b')).symm.trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun h => O.hom ≫ h) (OutsideNegativeMap.restriction f 0 h₀ a' b' (outside k h₀k a b))))
  have hL : d.map (.mk a) (.mk b) ≫ (R ≫ (S ≫ G)) =
      NegativeFaceRelations.leftRestriction f 0 k h₀ h₀k a b :=
    (Category.assoc (d.map (.mk a) (.mk b)) R (S ≫ G)).symm.trans
      ((Category.assoc (d.map (.mk a) (.mk b) ≫ R) S G).symm.trans
        ((congrArg (fun h => h ≫ G) hS).trans
          ((Category.assoc _ _ _).trans (congrArg (fun h => dl.map (.mk a) (.mk b) ≫ h) hN))))
  have hR : NegativeFaceRelations.rightRestriction f 0 k hk h₀k a b =
      d.map (.mk a) (.mk b) ≫ (M ≫ T) :=
    congrArg (fun h => d.map (.mk a) (.mk b) ≫ h)
      ((Category.assoc
        (OrdinalFace.negativeIso k ((OrdinalFace.embedding (0 : Fin (n + 2))) a)
          ((OrdinalFace.embedding (0 : Fin (n + 2))) b)).hom
        (negativeMap f k hk ((OrdinalFace.embedding (0 : Fin (n + 2))) a)
          ((OrdinalFace.embedding (0 : Fin (n + 2))) b)) T).symm.trans
            (congrArg (fun h => h ≫ T) (negativeMap_readback f k hk
              ((OrdinalFace.embedding (0 : Fin (n + 2))) a) ((OrdinalFace.embedding (0 : Fin (n + 2))) b))))
  exact hL.trans ((NegativeFaceRelations.restriction_agreement f 0 k h₀ hk h₀k a b).trans hR)

end CategoryTheory.CoherentRealization.FirstFaceRestriction
