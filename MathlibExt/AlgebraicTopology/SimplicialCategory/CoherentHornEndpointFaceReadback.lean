/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornOrderedMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentOutsideFaceMapCongruence

/-!
# Whole readback along the two actual supplied endpoint faces

The first and last ordinal face Hom isomorphisms read their entire
original supplied face maps back, at arbitrary original source labels.
No source interval order or Kan assumption is required.
-/

noncomputable section
universe u
open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HornEndpointFaceReadback
open SimplicialEnrichment
variable {n : ℕ}

private theorem first_ne_zero (a : Fin (n + 2)) : (0 : Fin (n + 3)).succAbove a ≠ 0 := by
  rw [Fin.succAbove_zero]
  exact Fin.succ_ne_zero a

private theorem last_ne_last (a : Fin (n + 2)) : (Fin.last (n + 2)).succAbove a ≠ Fin.last (n + 2) := by
  rw [Fin.succAbove_last]
  exact ne_of_lt (Fin.castSucc_lt_last a)

variable {C : Carrier.{u}} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)

/-- The actual first endpoint-face reading restricts to the entire original supplied first face Hom map. -/
theorem first (hi₀ : i ≠ 0) (a b : Fin (n + 2)) :
    (coherentSimplexMap (SimplexCategory.δ (0 : Fin (n + 3)))).map (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) ≫
      HornOrderedMaps.firstMap f hi₀ ((0 : Fin (n + 3)).succAbove a) ((0 : Fin (n + 3)).succAbove b)
        (first_ne_zero a) (first_ne_zero b) =
      HornHomFaces.faceMap f 0 hi₀.symm (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) := by
  let ha : (ULift.up (0 : Fin (n + 3)) : ULift.{u} (Fin (n + 3))) < (OrdinalFace.embedding (0 : Fin (n +
    3))) (ULift.up.{u} a) := by
    change (0 : Fin (n + 3)) < (0 : Fin (n + 3)).succAbove a
    rw [Fin.succAbove_zero]
    exact Fin.succ_pos a
  let O := IntervalFaceCover.outsideIso (0 : Fin (n + 3)) (ULift.up.{u} a) (ULift.up.{u} b) (Or.inl ha)
  let M := HornOutsideIntervals.faceMap f 0 hi₀.symm (ULift.up.{u} a) (ULift.up.{u} b) (Or.inl ha) rfl rfl
  have hpA : ((0 : Fin (n + 3)).succAbove a).pred (first_ne_zero a) = a := by
    simp only [Fin.succAbove_zero, Fin.pred_succ]
  have hpB : ((0 : Fin (n + 3)).succAbove b).pred (first_ne_zero b) = b := by
    simp only [Fin.succAbove_zero, Fin.pred_succ]
  have hM : HornOrderedMaps.firstMap f hi₀ ((0 : Fin (n + 3)).succAbove a) ((0 : Fin (n + 3)).succAbove b)
      (first_ne_zero a) (first_ne_zero b) = M :=
    OutsideFaceMapCongruence.source_eq f 0 hi₀.symm
      (ULift.up (((0 : Fin (n + 3)).succAbove a).pred (first_ne_zero a)))
      (ULift.up (((0 : Fin (n + 3)).succAbove b).pred (first_ne_zero b))) (ULift.up a) (ULift.up b)
      (ULift.ext hpA) (ULift.ext hpB)
      (Or.inl (show (ULift.up (0 : Fin (n + 3)) : ULift.{u} (Fin (n + 3))) <
        (OrdinalFace.embedding 0) (ULift.up (((0 : Fin (n + 3)).succAbove a).pred (first_ne_zero a))) from by
          change (0 : Fin (n + 3)) < (0 : Fin (n + 3)).succAbove (((0 : Fin (n + 3)).succAbove a).pred
            (first_ne_zero a))
          have hE : (0 : Fin (n + 3)).succAbove (((0 : Fin (n + 3)).succAbove a).pred (first_ne_zero a)) =
            (0 : Fin (n + 3)).succAbove a :=
            (congrFun Fin.succAbove_zero (((0 : Fin (n + 3)).succAbove a).pred (first_ne_zero a))).trans
              (Fin.succ_pred ((0 : Fin (n + 3)).succAbove a) (first_ne_zero a))
          exact (congrArg (fun x : Fin (n + 3) => (0 : Fin (n + 3)) < x) hE).mpr
            (Fin.pos_iff_ne_zero.mpr (first_ne_zero a)))) (Or.inl ha)
      (Fin.succ_pred ((0 : Fin (n + 3)).succAbove a) (first_ne_zero a))
      (Fin.succ_pred ((0 : Fin (n + 3)).succAbove b) (first_ne_zero b)) rfl rfl
  have hE : O.hom = (coherentSimplexMap (SimplexCategory.δ (0 : Fin (n + 3)))).map (.mk (ULift.up.{u} a))
    (.mk (ULift.up.{u} b)) :=
    IntervalFaceCover.outsideIso_operator 0 (ULift.up a) (ULift.up b) (Or.inl ha)
  have h := HornOutsideIntervals.faceMap_readback f 0 hi₀.symm (ULift.up.{u} a) (ULift.up.{u} b) (Or.inl ha) rfl rfl
  change O.hom ≫ 𝟙 _ ≫ M = HornHomFaces.faceMap f 0 hi₀.symm (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) ≫ 𝟙 _ at h
  have hR : O.hom ≫ M = HornHomFaces.faceMap f 0 hi₀.symm (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) :=
    (congrArg (fun g => O.hom ≫ g) (Category.id_comp M)).symm.trans (h.trans (Category.comp_id _))
  exact (congrArg (fun g => (coherentSimplexMap (SimplexCategory.δ (0 : Fin (n + 3)))).map
    (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) ≫ g) hM).trans
      ((congrArg (fun g => g ≫ M) hE).symm.trans hR)

/-- The actual last endpoint-face reading restricts to the entire original supplied last face Hom map. -/
theorem last (hiₙ : i ≠ Fin.last (n + 2)) (a b : Fin (n + 2)) :
    (coherentSimplexMap (SimplexCategory.δ (Fin.last (n + 2)))).map (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) ≫
      HornOrderedMaps.lastMap f hiₙ ((Fin.last (n + 2)).succAbove a) ((Fin.last (n + 2)).succAbove b)
        (last_ne_last a) (last_ne_last b) =
      HornHomFaces.faceMap f (Fin.last (n + 2)) hiₙ.symm (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) := by
  let hb : (OrdinalFace.embedding (Fin.last (n + 2))) (ULift.up.{u} b) <
      (ULift.up (Fin.last (n + 2)) : ULift.{u} (Fin (n + 3))) := by
    change (Fin.last (n + 2)).succAbove b < Fin.last (n + 2)
    simpa only [Fin.succAbove_last] using Fin.castSucc_lt_last b
  let O := IntervalFaceCover.outsideIso (Fin.last (n + 2)) (ULift.up.{u} a) (ULift.up.{u} b) (Or.inr hb)
  let M := HornOutsideIntervals.faceMap f (Fin.last (n + 2)) hiₙ.symm (ULift.up.{u} a) (ULift.up.{u} b)
    (Or.inr hb) rfl rfl
  have hpA : ((Fin.last (n + 2)).succAbove a).castPred (last_ne_last a) = a := by
    simp only [Fin.succAbove_last, Fin.castPred_castSucc]
  have hpB : ((Fin.last (n + 2)).succAbove b).castPred (last_ne_last b) = b := by
    simp only [Fin.succAbove_last, Fin.castPred_castSucc]
  have hM : HornOrderedMaps.lastMap f hiₙ ((Fin.last (n + 2)).succAbove a) ((Fin.last (n + 2)).succAbove b)
      (last_ne_last a) (last_ne_last b) = M :=
    OutsideFaceMapCongruence.source_eq f (Fin.last (n + 2)) hiₙ.symm
      (ULift.up (((Fin.last (n + 2)).succAbove a).castPred (last_ne_last a)))
      (ULift.up (((Fin.last (n + 2)).succAbove b).castPred (last_ne_last b))) (ULift.up a) (ULift.up b)
      (ULift.ext hpA) (ULift.ext hpB)
      (Or.inr (show (OrdinalFace.embedding (Fin.last (n + 2)))
        (ULift.up (((Fin.last (n + 2)).succAbove b).castPred (last_ne_last b))) <
          (ULift.up (Fin.last (n + 2)) : ULift.{u} (Fin (n + 3))) from by
            change (Fin.last (n + 2)).succAbove (((Fin.last (n + 2)).succAbove b).castPred (last_ne_last b))
              < Fin.last (n + 2)
            have hE : (Fin.last (n + 2)).succAbove (((Fin.last (n + 2)).succAbove b).castPred (last_ne_last
              b)) = (Fin.last (n + 2)).succAbove b :=
              (congrFun Fin.succAbove_last (((Fin.last (n + 2)).succAbove b).castPred (last_ne_last b))).trans
                (Fin.castSucc_castPred ((Fin.last (n + 2)).succAbove b) (last_ne_last b))
            exact (congrArg (fun x : Fin (n + 3) => x < Fin.last (n + 2)) hE).mpr
              (Fin.lt_last_iff_ne_last.mpr (last_ne_last b)))) (Or.inr hb)
      ((congrFun Fin.succAbove_last (((Fin.last (n + 2)).succAbove a).castPred (last_ne_last a))).trans
        (Fin.castSucc_castPred ((Fin.last (n + 2)).succAbove a) (last_ne_last a)))
      ((congrFun Fin.succAbove_last (((Fin.last (n + 2)).succAbove b).castPred (last_ne_last b))).trans
        (Fin.castSucc_castPred ((Fin.last (n + 2)).succAbove b) (last_ne_last b))) rfl rfl
  have hE : O.hom = (coherentSimplexMap (SimplexCategory.δ (Fin.last (n + 2)))).map (.mk (ULift.up.{u} a))
    (.mk (ULift.up.{u} b)) :=
    IntervalFaceCover.outsideIso_operator (Fin.last (n + 2)) (ULift.up a) (ULift.up b) (Or.inr hb)
  have h := HornOutsideIntervals.faceMap_readback f (Fin.last (n + 2)) hiₙ.symm (ULift.up.{u} a)
    (ULift.up.{u} b) (Or.inr hb) rfl rfl
  change O.hom ≫ 𝟙 _ ≫ M = HornHomFaces.faceMap f (Fin.last (n + 2)) hiₙ.symm (.mk (ULift.up.{u} a)) (.mk
    (ULift.up.{u} b)) ≫ 𝟙 _ at h
  have hR : O.hom ≫ M = HornHomFaces.faceMap f (Fin.last (n + 2)) hiₙ.symm (.mk (ULift.up.{u} a)) (.mk
    (ULift.up.{u} b)) :=
    (congrArg (fun g => O.hom ≫ g) (Category.id_comp M)).symm.trans (h.trans (Category.comp_id _))
  exact (congrArg (fun g => (coherentSimplexMap (SimplexCategory.δ (Fin.last (n + 2)))).map
    (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) ≫ g) hM).trans
      ((congrArg (fun g => g ≫ M) hE).symm.trans hR)

end CategoryTheory.CoherentRealization.HornEndpointFaceReadback
