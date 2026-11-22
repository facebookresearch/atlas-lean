/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.SimplexPullbackFacesWeak

/-!
# Literal over-pullback maps and full original subcomplex preimages

The native over-pullback map of an original subcomplex inclusion is
identified by a genuine arrow Iso with the entire original preimage
inclusion. Both source and target comparisons and every original base
map are retained. Its weak-class readback is therefore exact, including
the original horn maps needed by the dependent-product lifting proof.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace SSet.OverSubcomplex

variable {E B Y : SSet.{u}} (p : E ⟶ B) (b : Y ⟶ B) (K : Y.Subcomplex)

/-- The SAME original subcomplex inclusion as a full original over-category arrow. -/
def arrow : Over.mk (K.ι ≫ b) ⟶ Over.mk b := Over.homMk K.ι (by rfl)

/-- The literal native over-pullback map of that SAME full original arrow. -/
def map : pullback (K.ι ≫ b) p ⟶ pullback b p := ((Over.pullback p).map (arrow b K)).left

/-- The full first projection retains the original complete subcomplex inclusion. -/
theorem map_fst : map p b K ≫ pullback.fst b p = pullback.fst (K.ι ≫ b) p ≫ K.ι :=
  pullback.lift_fst _ _ _

/-- The full second projection is the SAME original source projection. -/
theorem map_snd : map p b K ≫ pullback.snd b p = pullback.snd (K.ι ≫ b) p :=
  pullback.lift_snd _ _ _

private theorem preimageSquare : IsPullback
    (K.fromPreimage (pullback.snd p b))
    ((K.preimage (pullback.snd p b)).ι ≫ pullback.fst p b) (K.ι ≫ b) p :=
  ((Subcomplex.preimage_isPullback K (pullback.snd p b)).paste_horiz (IsPullback.of_hasPullback p b)).flip

/-- Both full maps identify the entire original preimage with the SAME native over-pullback source. -/
def sourceIso : (K.preimage (pullback.snd p b) : SSet.{u}) ≅ pullback (K.ι ≫ b) p :=
  (preimageSquare p b K).isoPullback

/-- The actual source comparison retains the full original face/horn coefficient projection. -/
theorem sourceIso_fst : (sourceIso p b K).hom ≫ pullback.fst (K.ι ≫ b) p =
    K.fromPreimage (pullback.snd p b) := (preimageSquare p b K).isoPullback_hom_fst

/-- The actual source comparison retains the SAME complete original source projection. -/
theorem sourceIso_snd : (sourceIso p b K).hom ≫ pullback.snd (K.ι ≫ b) p =
    (K.preimage (pullback.snd p b)).ι ≫ pullback.fst p b := (preimageSquare p b K).isoPullback_hom_snd

/-- The SAME original source, map and whole native target symmetry give the exact original preimage inclusion. -/
theorem sourceIso_map : (sourceIso p b K).hom ≫ map p b K ≫ (pullbackSymmetry b p).hom =
    (K.preimage (pullback.snd p b)).ι := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_fst, map_snd, sourceIso_snd]
  · rw [Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_snd,
      map_fst, ← Category.assoc, sourceIso_fst]
    exact Subcomplex.fromPreimage_ι _ _

/-- The genuine whole original arrow Iso retains the SAME native over-pullback map. -/
def arrowIso : Arrow.mk (K.preimage (pullback.snd p b)).ι ≅ Arrow.mk (map p b K) :=
  Arrow.isoMk (sourceIso p b K) (pullbackSymmetry b p).symm (by
    apply (cancel_mono (pullbackSymmetry b p).hom).mp
    change (sourceIso p b K).hom ≫ map p b K ≫ (pullbackSymmetry b p).hom =
      ((K.preimage (pullback.snd p b)).ι ≫ (pullbackSymmetry b p).inv) ≫ (pullbackSymmetry b p).hom
    rw [Category.assoc (K.preimage (pullback.snd p b)).ι, Iso.inv_hom_id, Category.comp_id]
    exact sourceIso_map p b K)

/-- Literal native over-pullback weakness is precisely weakness of the SAME
full original subcomplex preimage inclusion, at every original base map. -/
theorem map_weak_iff : realizationWeakEquivalences (map p b K) ↔
    realizationWeakEquivalences (K.preimage (pullback.snd p b)).ι :=
  (realizationWeakEquivalences.arrow_mk_iso_iff (arrowIso p b K)).symm

end SSet.OverSubcomplex
