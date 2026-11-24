/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentCommonIntervalMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornOutsideIntervals

/-!
# The original outside-face extraction agrees with the common interval map

The entire Hom map obtained directly from a supplied outside face equals
the map obtained through its actual common ordinal face. The equality
uses the original face operator and both whole Hom inverse equations.
No compatibility or enriched-filler conclusion is supplied as data.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OutsideFaceAgreement
open SimplicialEnrichment HornHomFaces
variable {C : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (j k : Fin (n + 3)) (hj : j ≠ i) (hjk : j < k)
  (a b : ULift.{u} (Fin (n + 1)))
  (houtj : (ULift.up j : ULift.{u} (Fin (n + 3))) < TwoOutsideFaces.point j k hjk a ∨
    TwoOutsideFaces.point j k hjk b < ULift.up j)
  (houtk : (ULift.up k : ULift.{u} (Fin (n + 3))) < TwoOutsideFaces.point j k hjk a ∨
    TwoOutsideFaces.point j k hjk b < ULift.up k)

/-- Direct extraction from the first supplied outside face is precisely the entire common original interval map. -/
theorem left_agreement :
    HornOutsideIntervals.faceMap f j hj
      ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) a)
      ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) b) houtj
      (a := (TwoOutsideFaces.point j k hjk a).down)
      (b := (TwoOutsideFaces.point j k hjk b).down) rfl rfl =
        CommonIntervalMaps.leftMap f j k hj hjk a b houtj houtk := by
  let d := coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk)))
  let E := IntervalFaceCover.outsideIso (k.pred (Fin.ne_zero_of_lt hjk)) a b
    (TwoOutsideFaces.inner_outside j k hjk a b houtk)
  let O := IntervalFaceCover.outsideIso j
    ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) a)
    ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) b) houtj
  let M := retargetMap (HornFaces.faceFunctor f j hj) (d.obj (.mk a)) (d.obj (.mk b))
    (HornFaces.faceFunctor_obj f j hj (d.obj (.mk a)))
    (HornFaces.faceFunctor_obj f j hj (d.obj (.mk b)))
  simp only [HornOutsideIntervals.faceMap, eqToHom_refl, Category.id_comp, Category.comp_id]
  change O.inv ≫ M = (O.inv ≫ E.inv) ≫ retargetMap (d ≫ HornFaces.faceFunctor f j hj) (.mk a) (.mk b)
    (HornFaces.faceFunctor_obj f j hj (d.obj (.mk a)))
    (HornFaces.faceFunctor_obj f j hj (d.obj (.mk b)))
  have hE : E.hom = d.map (.mk a) (.mk b) :=
    IntervalFaceCover.outsideIso_operator (k.pred (Fin.ne_zero_of_lt hjk)) a b
      (TwoOutsideFaces.inner_outside j k hjk a b houtk)
  have ht := HornMapAlgebra.retargetMap_precomp d (HornFaces.faceFunctor f j hj) (.mk a) (.mk b)
    (HornFaces.faceFunctor_obj f j hj (d.obj (.mk a)))
    (HornFaces.faceFunctor_obj f j hj (d.obj (.mk b)))
  calc
    O.inv ≫ M = O.inv ≫ (𝟙 _ ≫ M) := congrArg (fun t => O.inv ≫ t) (Category.id_comp M).symm
    _ = O.inv ≫ ((E.inv ≫ E.hom) ≫ M) :=
      congrArg (fun t => O.inv ≫ (t ≫ M)) E.inv_hom_id.symm
    _ = O.inv ≫ (E.inv ≫ (E.hom ≫ M)) :=
      congrArg (fun t => O.inv ≫ t) (Category.assoc _ _ _)
    _ = (O.inv ≫ E.inv) ≫ (E.hom ≫ M) := (Category.assoc _ _ _).symm
    _ = (O.inv ≫ E.inv) ≫ (d.map (.mk a) (.mk b) ≫ M) :=
      congrArg (fun t => (O.inv ≫ E.inv) ≫ (t ≫ M)) hE
    _ = _ := congrArg (fun t => (O.inv ≫ E.inv) ≫ t) ht

end CategoryTheory.CoherentRealization.OutsideFaceAgreement
