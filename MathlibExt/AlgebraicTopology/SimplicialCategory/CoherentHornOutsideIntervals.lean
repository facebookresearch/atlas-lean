/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornHomFaces
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentIntervalFaceCover

/-!
# The actual entire nonexceptional Hom maps of an inner coherent horn

Every original interval except the two outer endpoints is carried by an
available endpoint face. Its entire Hom map is extracted from the actual
horn map by the proved outside-face isomorphism. Both original endpoint
labels are retained. No Kan structure or enriched-filler conclusion is
needed for this extraction.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HornOutsideIntervals
open SimplicialEnrichment
variable {C : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)

/-- The whole original outside-face Hom map, with both supplied original endpoint labels
explicit. -/
def faceMap (j : Fin (n + 3)) (hj : j ≠ i) (a' b' : ULift.{u} (Fin (n + 2)))
    (h : (ULift.up j : ULift.{u} (Fin (n + 3))) < (OrdinalFace.embedding j) a' ∨
      (OrdinalFace.embedding j) b' < ULift.up j)
    {a b : Fin (n + 3)} (ha : j.succAbove a'.down = a) (hb : j.succAbove b'.down = b) :
    nerve (SimplicialThickening.Path (ULift.up.{u} a) (ULift.up.{u} b)) ⟶
      (HornFaces.object f a ⟶[SSet.{u}] HornFaces.object f b) :=
  eqToHom (congrArg₂ (fun a b : Fin (n + 3) =>
      nerve (SimplicialThickening.Path (ULift.up.{u} a) (ULift.up.{u} b))) ha.symm hb.symm) ≫
    (IntervalFaceCover.outsideIso j a' b' h).inv ≫
      HornHomFaces.faceMap f j hj (.mk a') (.mk b') ≫
        eqToHom (congrArg₂ (fun a b : C => a ⟶[SSet.{u}] b)
          (congrArg (HornFaces.object f) ha) (congrArg (HornFaces.object f) hb))

/-- The whole outside-face extraction reads back precisely the original supplied face Hom map. -/
theorem faceMap_readback (j : Fin (n + 3)) (hj : j ≠ i) (a' b' : ULift.{u} (Fin (n + 2)))
    (h : (ULift.up j : ULift.{u} (Fin (n + 3))) < (OrdinalFace.embedding j) a' ∨
      (OrdinalFace.embedding j) b' < ULift.up j)
    {a b : Fin (n + 3)} (ha : j.succAbove a'.down = a) (hb : j.succAbove b'.down = b) :
    (IntervalFaceCover.outsideIso j a' b' h).hom ≫
      eqToHom (congrArg₂ (fun a b : Fin (n + 3) =>
        nerve (SimplicialThickening.Path (ULift.up.{u} a) (ULift.up.{u} b))) ha hb) ≫
          faceMap f j hj a' b' h ha hb =
      HornHomFaces.faceMap f j hj (.mk a') (.mk b') ≫
        eqToHom (congrArg₂ (fun a b : C => a ⟶[SSet.{u}] b)
          (congrArg (HornFaces.object f) ha) (congrArg (HornFaces.object f) hb)) := by
  subst a
  subst b
  change (IntervalFaceCover.outsideIso j a' b' h).hom ≫ 𝟙 _ ≫
      (𝟙 _ ≫ (IntervalFaceCover.outsideIso j a' b' h).inv ≫
        HornHomFaces.faceMap f j hj (.mk a') (.mk b') ≫ 𝟙 _) =
      HornHomFaces.faceMap f j hj (.mk a') (.mk b') ≫ 𝟙 _
  simp only [Category.comp_id, Category.id_comp]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ HornHomFaces.faceMap f j hj (.mk a') (.mk b'))
      (IntervalFaceCover.outsideIso j a' b' h).hom_inv_id).trans (Category.id_comp _))

/-- The actual inner horn supplies every whole ordered Hom interval except the two outer
endpoints. -/
def homMap (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2))
    (a b : Fin (n + 3)) (hab : a ≤ b) (h : a ≠ 0 ∨ b ≠ Fin.last (n + 2)) :
    nerve (SimplicialThickening.Path (ULift.up.{u} a) (ULift.up.{u} b)) ⟶
      (HornFaces.object f a ⟶[SSet.{u}] HornFaces.object f b) := by
  classical
  by_cases ha : a = 0
  · have hb : b ≠ Fin.last (n + 2) := h.resolve_left (not_not_intro ha)
    have haₙ : a ≠ Fin.last (n + 2) := by
      subst a
      intro hlast
      have hval : (0 : ℕ) = n + 2 := congrArg Fin.val hlast
      omega
    refine faceMap f (Fin.last (n + 2)) hiₙ.symm
      (ULift.up (a.castPred haₙ)) (ULift.up (b.castPred hb)) (Or.inr ?_) ?_ ?_
    · change (Fin.last (n + 2)).succAbove (b.castPred hb) < Fin.last (n + 2)
      simpa only [Fin.succAbove_last, Fin.castSucc_castPred] using (Fin.lt_last_iff_ne_last.mpr hb)
    · simpa only [ULift.down_up, Fin.succAbove_last] using Fin.castSucc_castPred a haₙ
    · simpa only [ULift.down_up, Fin.succAbove_last] using Fin.castSucc_castPred b hb
  · have hb : b ≠ 0 := by
      intro hb
      subst b
      exact ha (le_antisymm hab (Fin.zero_le _))
    refine faceMap f 0 hi₀.symm (ULift.up (a.pred ha)) (ULift.up (b.pred hb)) (Or.inl ?_) ?_ ?_
    · change (0 : Fin (n + 3)) < (0 : Fin (n + 3)).succAbove (a.pred ha)
      simpa only [Fin.succAbove_zero, Fin.succ_pred] using (Fin.pos_iff_ne_zero.mpr ha)
    · exact Fin.succ_pred a ha
    · exact Fin.succ_pred b hb

end CategoryTheory.CoherentRealization.HornOutsideIntervals
