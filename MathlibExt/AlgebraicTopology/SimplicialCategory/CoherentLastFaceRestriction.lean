/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentOutsideNegativeRetarget

/-!
# The actual last endpoint-face Hom map restricts to supplied faces

The original last endpoint face carries every whole interval ending
before that endpoint. Its actual Hom map agrees with the supported short
leg of every other available face. Both original endpoint transports and
the actual horn's common-face relation are retained. No Kan or comparison
outcome is a premise.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.LastFaceRestriction
open SimplicialEnrichment HornHomFaces
variable {C : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (hₙ : Fin.last (n + 2) ≠ i) (k : Fin (n + 3)) (hkₙ : k < Fin.last (n + 2))
  (a b : ULift.{u} (Fin (n + 1)))

/-- The actual last face covers the same original interval through its actual common-face preimages. -/
theorem outside :
    (ULift.up (Fin.last (n + 2)) : ULift.{u} (Fin (n + 3))) <
      (OrdinalFace.embedding (Fin.last (n + 2))) ((OrdinalFace.embedding (k.castPred (Fin.ne_last_of_lt hkₙ))) a) ∨
    (OrdinalFace.embedding (Fin.last (n + 2))) ((OrdinalFace.embedding (k.castPred (Fin.ne_last_of_lt hkₙ))) b) <
      ULift.up (Fin.last (n + 2)) := by
  right
  change (Fin.last (n + 2)).succAbove ((OrdinalFace.embedding (k.castPred (Fin.ne_last_of_lt hkₙ))) b).down <
    Fin.last (n + 2)
  simpa only [Fin.succAbove_last] using Fin.castSucc_lt_last ((OrdinalFace.embedding (k.castPred
    (Fin.ne_last_of_lt hkₙ))) b).down

/-- The actual last endpoint-face map on the same individual original common interval. -/
def map :
    nerve (SimplicialThickening.Path (TwoOutsideFaces.point k (Fin.last (n + 2)) hkₙ a)
      (TwoOutsideFaces.point k (Fin.last (n + 2)) hkₙ b)) ⟶
    (HornFaces.object f (TwoOutsideFaces.point k (Fin.last (n + 2)) hkₙ a).down ⟶[SSet.{u}]
      HornFaces.object f (TwoOutsideFaces.point k (Fin.last (n + 2)) hkₙ b).down) :=
  HornOutsideIntervals.faceMap f (Fin.last (n + 2)) hₙ
    ((OrdinalFace.embedding (k.castPred (Fin.ne_last_of_lt hkₙ))) a)
    ((OrdinalFace.embedding (k.castPred (Fin.ne_last_of_lt hkₙ))) b) (outside k hkₙ a b)
    (common_vertex k (Fin.last (n + 2)) hkₙ a.down).symm
    (common_vertex k (Fin.last (n + 2)) hkₙ b.down).symm

/-- The actual last endpoint-face map restricts to the supplied short leg, retaining the same whole original
  Hom and endpoints. -/
theorem restriction (hk : k ≠ i) :
    (coherentSimplexMap (SimplexCategory.δ k)).map
      ((coherentSimplexMap (SimplexCategory.δ ((Fin.last (n + 2)).pred (Fin.ne_zero_of_lt hkₙ)))).obj (.mk a))
      ((coherentSimplexMap (SimplexCategory.δ ((Fin.last (n + 2)).pred (Fin.ne_zero_of_lt hkₙ)))).obj (.mk b)) ≫
        map f hₙ k hkₙ a b =
    HornHomFaces.faceMap f k hk
      ((coherentSimplexMap (SimplexCategory.δ ((Fin.last (n + 2)).pred (Fin.ne_zero_of_lt hkₙ)))).obj (.mk a))
      ((coherentSimplexMap (SimplexCategory.δ ((Fin.last (n + 2)).pred (Fin.ne_zero_of_lt hkₙ)))).obj (.mk b)) := by
  let dl := coherentSimplexMap (SimplexCategory.δ ((Fin.last (n + 2)).pred (Fin.ne_zero_of_lt hkₙ)))
  let dr := coherentSimplexMap (SimplexCategory.δ (k.castPred (Fin.ne_last_of_lt hkₙ)))
  let a' := (OrdinalFace.embedding (k.castPred (Fin.ne_last_of_lt hkₙ))) a
  let b' := (OrdinalFace.embedding (k.castPred (Fin.ne_last_of_lt hkₙ))) b
  let E := IntervalFaceCover.outsideIso ((Fin.last (n + 2)).pred (Fin.ne_zero_of_lt hkₙ)) a b
    (Or.inr (show (OrdinalFace.embedding ((Fin.last (n + 2)).pred (Fin.ne_zero_of_lt hkₙ))) b <
        (ULift.up ((Fin.last (n + 2)).pred (Fin.ne_zero_of_lt hkₙ)) : ULift.{u} (Fin (n + 2))) from by
      change (Fin.last (n + 1)).succAbove b.down < Fin.last (n + 1)
      simpa only [Fin.succAbove_last] using Fin.castSucc_lt_last b.down))
  have hE : E.hom = dl.map (.mk a) (.mk b) :=
    IntervalFaceCover.outsideIso_operator ((Fin.last (n + 2)).pred (Fin.ne_zero_of_lt hkₙ)) a b _
  let _ : IsIso (dl.map (.mk a) (.mk b)) := hE ▸ E.isIso_hom
  let G := map f hₙ k hkₙ a b
  let R := (coherentSimplexMap (SimplexCategory.δ k)).map (dl.obj (.mk a)) (dl.obj (.mk b))
  let M := HornHomFaces.faceMap f k hk (dl.obj (.mk a)) (dl.obj (.mk b))
  let S := eqToHom (congrArg₂ (fun a b : Fin (n + 3) => nerve (SimplicialThickening.Path (ULift.up.{u} a)
    (ULift.up.{u} b)))
    (common_vertex k (Fin.last (n + 2)) hkₙ a.down).symm
    (common_vertex k (Fin.last (n + 2)) hkₙ b.down).symm)
  let T := eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y)
    (congrArg (HornFaces.object f) (common_vertex k (Fin.last (n + 2)) hkₙ a.down).symm)
    (congrArg (HornFaces.object f) (common_vertex k (Fin.last (n + 2)) hkₙ b.down).symm))
  let O := OrdinalFace.negativeIso (Fin.last (n + 2)) a' b'
  let N := negativeMap f (Fin.last (n + 2)) hₙ a' b'
  apply (cancel_epi (dl.map (.mk a) (.mk b))).mp
  have hS : (dr.map (.mk a) (.mk b) ≫
      (coherentSimplexMap (SimplexCategory.δ (Fin.last (n + 2)))).map (.mk a') (.mk b')) ≫ S =
      dl.map (.mk a) (.mk b) ≫ R := CommonIntervalMaps.operator_eq k (Fin.last (n + 2)) hkₙ a b
  have hN : (coherentSimplexMap (SimplexCategory.δ (Fin.last (n + 2)))).map (.mk a') (.mk b') ≫ (S ≫ G) =
      O.hom ≫ (N ≫ T) :=
    (congrArg (fun h => h ≫ (S ≫ G)) (OrdinalFace.negativeIso_operator (Fin.last (n + 2)) a' b')).symm.trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun h => O.hom ≫ h)
          (OutsideNegativeRetarget.restriction f (Fin.last (n + 2)) hₙ a' b' (outside k hkₙ a b)
            (common_vertex k (Fin.last (n + 2)) hkₙ a.down).symm
            (common_vertex k (Fin.last (n + 2)) hkₙ b.down).symm)))
  have hL : NegativeFaceRelations.leftRestriction f k (Fin.last (n + 2)) hk hkₙ a b =
      dl.map (.mk a) (.mk b) ≫ M :=
    congrArg (fun h => dl.map (.mk a) (.mk b) ≫ h) (negativeMap_readback f k hk
      ((OrdinalFace.embedding ((Fin.last (n + 2)).pred (Fin.ne_zero_of_lt hkₙ))) a)
      ((OrdinalFace.embedding ((Fin.last (n + 2)).pred (Fin.ne_zero_of_lt hkₙ))) b))
  have hR : NegativeFaceRelations.rightRestriction f k (Fin.last (n + 2)) hₙ hkₙ a b =
      dl.map (.mk a) (.mk b) ≫ (R ≫ G) :=
    (congrArg (fun h => dr.map (.mk a) (.mk b) ≫ h) hN).symm.trans
      ((Category.assoc _ _ _).symm.trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun h => h ≫ G) hS).trans (Category.assoc _ _ _))))
  exact (hL.symm.trans
    ((NegativeFaceRelations.restriction_agreement f k (Fin.last (n + 2)) hk hₙ hkₙ a b).trans hR)).symm

end CategoryTheory.CoherentRealization.LastFaceRestriction
