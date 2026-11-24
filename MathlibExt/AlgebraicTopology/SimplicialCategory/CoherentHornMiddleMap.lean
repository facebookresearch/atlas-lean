/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornShortLegs
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentOtherOutsideFaceAgreement

/-!
# The same whole middle Hom map in the two supplied endpoint faces

The actual interior vertices have explicit preimages in the common
first-and-last ordinal face. The whole Hom maps from both supplied
endpoint faces agree by the original horn's common-face relation.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HornMiddleMap
open SimplicialEnrichment HornBoxFaces
variable {n : ℕ}

/-- Removing the last original label leaves a supplied interior vertex nonzero. -/
theorem castPred_ne_zero (b : Interior.{u} n) :
    (HornBoxFaces.vertex b).castPred (vertex_ne_last b) ≠ 0 := by
  intro h
  have h' := Fin.castSucc_castPred (HornBoxFaces.vertex b) (vertex_ne_last b)
  rw [h] at h'
  exact vertex_ne_zero b h'.symm

/-- The same individual interior vertex in the common face omitting both outer labels. -/
def preimage (b : Interior.{u} n) : ULift.{u} (Fin (n + 1)) :=
  ULift.up (((HornBoxFaces.vertex b).castPred (vertex_ne_last b)).pred (castPred_ne_zero b))

/-- Reading that common vertex through the supplied last face gives its original last-face preimage. -/
theorem last_preimage (b : Interior.{u} n) :
    (OrdinalFace.embedding (0 : Fin (n + 2))) (preimage b) =
      ULift.up ((HornBoxFaces.vertex b).castPred (vertex_ne_last b)) := by
  apply ULift.ext
  change (((HornBoxFaces.vertex b).castPred (vertex_ne_last b)).pred (castPred_ne_zero b)).succ = _
  exact Fin.succ_pred _ _

/-- Reading the same common vertex through the supplied first face gives its original first-face preimage. -/
theorem first_preimage (b : Interior.{u} n) :
    (OrdinalFace.embedding (Fin.last (n + 1))) (preimage b) =
      ULift.up ((HornBoxFaces.vertex b).pred (vertex_ne_zero b)) := by
  apply ULift.ext
  change (Fin.last (n + 1)).succAbove (((HornBoxFaces.vertex b).castPred (vertex_ne_last b)).pred
    (castPred_ne_zero b)) = _
  rw [Fin.succAbove_last]
  apply Fin.ext
  have h₁ := congrArg Fin.val (Fin.succ_pred (HornBoxFaces.vertex b) (vertex_ne_zero b))
  have h₂ := congrArg Fin.val (Fin.succ_pred ((HornBoxFaces.vertex b).castPred (vertex_ne_last b)) (castPred_ne_zero b))
  simp only [Fin.val_succ, Fin.coe_castPred] at h₁ h₂
  change (((HornBoxFaces.vertex b).castPred (vertex_ne_last b)).pred (castPred_ne_zero b)).val =
    ((HornBoxFaces.vertex b).pred (vertex_ne_zero b)).val
  omega

/-- The common first-and-last-face chart keeps exactly the supplied original interior vertex. -/
theorem point (b : Interior.{u} n) :
    TwoOutsideFaces.point (0 : Fin (n + 3)) (Fin.last (n + 2))
      (show (0 : Fin (n + 3)) < Fin.last (n + 2) from by change 0 < n + 2; omega) (preimage b) = b.val := by
  change (OrdinalFace.embedding (0 : Fin (n + 3)))
    ((OrdinalFace.embedding (Fin.last (n + 1))) (preimage b)) = b.val
  rw [first_preimage b]
  apply ULift.ext
  change ((HornBoxFaces.vertex b).pred (vertex_ne_zero b)).succ = HornBoxFaces.vertex b
  exact Fin.succ_pred _ _

variable {C : Carrier.{u}} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2))

/-- The whole middle Hom map read from the actual supplied first horn face. -/
def firstMap (b c : Interior.{u} n) :
    nerve (SimplicialThickening.Path b.val c.val) ⟶
      (HornFaces.object f (HornBoxFaces.vertex b) ⟶[SSet.{u}] HornFaces.object f (HornBoxFaces.vertex c)) :=
  HornOutsideIntervals.faceMap f (0 : Fin (n + 3)) hi₀.symm
    (ULift.up ((HornBoxFaces.vertex b).pred (vertex_ne_zero b)))
    (ULift.up ((HornBoxFaces.vertex c).pred (vertex_ne_zero c)))
    (Or.inl (show (ULift.up (0 : Fin (n + 3)) : ULift.{u} (Fin (n + 3))) <
        (OrdinalFace.embedding (0 : Fin (n + 3))) (ULift.up ((HornBoxFaces.vertex b).pred (vertex_ne_zero b))) from
      by
        change (0 : Fin (n + 3)) < (0 : Fin (n + 3)).succAbove ((HornBoxFaces.vertex b).pred (vertex_ne_zero b))
        simpa only [Fin.succAbove_zero, Fin.succ_pred] using (show (0 : Fin (n + 3)) < HornBoxFaces.vertex b
          from b.property.1)))
    (Fin.succ_pred (HornBoxFaces.vertex b) (vertex_ne_zero b)) (Fin.succ_pred (HornBoxFaces.vertex c)
      (vertex_ne_zero c))

/-- The same whole middle Hom map read from the actual supplied last horn face. -/
def lastMap (b c : Interior.{u} n) :
    nerve (SimplicialThickening.Path b.val c.val) ⟶
      (HornFaces.object f (HornBoxFaces.vertex b) ⟶[SSet.{u}] HornFaces.object f (HornBoxFaces.vertex c)) :=
  HornOutsideIntervals.faceMap f (Fin.last (n + 2)) hiₙ.symm
    (ULift.up ((HornBoxFaces.vertex b).castPred (vertex_ne_last b)))
    (ULift.up ((HornBoxFaces.vertex c).castPred (vertex_ne_last c)))
    (Or.inr (show (OrdinalFace.embedding (Fin.last (n + 2))) (ULift.up ((HornBoxFaces.vertex c).castPred
      (vertex_ne_last c))) <
        (ULift.up (Fin.last (n + 2)) : ULift.{u} (Fin (n + 3))) from
      by
        change (Fin.last (n + 2)).succAbove ((HornBoxFaces.vertex c).castPred (vertex_ne_last c)) < Fin.last (n + 2)
        simpa only [Fin.succAbove_last, Fin.castSucc_castPred] using (show HornBoxFaces.vertex c < Fin.last
          (n + 2) from c.property.2)))
    (by simpa only [Fin.succAbove_last] using Fin.castSucc_castPred (HornBoxFaces.vertex b) (vertex_ne_last b))
    (by simpa only [Fin.succAbove_last] using Fin.castSucc_castPred (HornBoxFaces.vertex c) (vertex_ne_last c))

/-- The two actual outside-face extractions agree at supplied original endpoints of their common face. -/
theorem direct_agreement (j k : Fin (n + 3)) (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k)
    (a' b' : ULift.{u} (Fin (n + 1)))
    (houtj : (ULift.up j : ULift.{u} (Fin (n + 3))) < TwoOutsideFaces.point j k hjk a' ∨
      TwoOutsideFaces.point j k hjk b' < ULift.up j)
    (houtk : (ULift.up k : ULift.{u} (Fin (n + 3))) < TwoOutsideFaces.point j k hjk a' ∨
      TwoOutsideFaces.point j k hjk b' < ULift.up k)
    {a b : Fin (n + 3)} (ha : (TwoOutsideFaces.point j k hjk a').down = a)
    (hb : (TwoOutsideFaces.point j k hjk b').down = b) :
    HornOutsideIntervals.faceMap f j hj
        ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) a')
        ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) b') houtj ha hb =
      HornOutsideIntervals.faceMap f k hk
        ((OrdinalFace.embedding (j.castPred (Fin.ne_last_of_lt hjk))) a')
        ((OrdinalFace.embedding (j.castPred (Fin.ne_last_of_lt hjk))) b')
        (OtherOutsideFaceAgreement.rightOutside j k hjk a' b' houtk)
        ((HornHomFaces.common_vertex j k hjk a'.down).symm.trans ha)
        ((HornHomFaces.common_vertex j k hjk b'.down).symm.trans hb) := by
  subst a
  subst b
  exact (OutsideFaceAgreement.left_agreement f j k hj hjk a' b' houtj houtk).trans
    ((CommonIntervalMaps.leftMap_eq_rightMap f j k hj hk hjk a' b' houtj houtk).trans
      (OtherOutsideFaceAgreement.right_agreement f j k hk hjk a' b' houtj houtk).symm)

/-- The actual common first-and-last-face Hom map, with both individual interior vertices retained. -/
theorem firstMap_eq_lastMap (b c : Interior.{u} n) : firstMap f hi₀ b c = lastMap f hiₙ b c := by
  let h : (0 : Fin (n + 3)) < Fin.last (n + 2) := by change 0 < n + 2; omega
  let hj : (ULift.up (0 : Fin (n + 3)) : ULift.{u} (Fin (n + 3))) <
      TwoOutsideFaces.point 0 (Fin.last (n + 2)) h (preimage b) ∨
    TwoOutsideFaces.point 0 (Fin.last (n + 2)) h (preimage c) < ULift.up 0 :=
      Or.inl (by rw [point b]; exact b.property.1)
  let hk : (ULift.up (Fin.last (n + 2)) : ULift.{u} (Fin (n + 3))) <
      TwoOutsideFaces.point 0 (Fin.last (n + 2)) h (preimage b) ∨
    TwoOutsideFaces.point 0 (Fin.last (n + 2)) h (preimage c) < ULift.up (Fin.last (n + 2)) :=
      Or.inr (by rw [point c]; exact c.property.2)
  have hp := direct_agreement f 0 (Fin.last (n + 2)) hi₀.symm hiₙ.symm h
    (preimage b) (preimage c) hj hk
    (a := HornBoxFaces.vertex b) (b := HornBoxFaces.vertex c)
    (congrArg ULift.down (point b)) (congrArg ULift.down (point c))
  have hl : (Fin.last (n + 2)).pred (Fin.ne_zero_of_lt h) = Fin.last (n + 1) := rfl
  have hz : (0 : Fin (n + 3)).castPred (Fin.ne_last_of_lt h) = 0 := rfl
  simpa only [firstMap, lastMap, hl, hz, first_preimage, last_preimage] using hp

end CategoryTheory.CoherentRealization.HornMiddleMap
