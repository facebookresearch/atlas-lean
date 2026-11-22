/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceCutReassembly

/-!
# Genuine full original necklace cut pushouts

The two SAME original cut maps form a genuine pushout into the original
necklace. Both full inverse reassembly charts retain their exact native
maps. Original maps into any target are uniquely determined by these
same two complete cuts.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace.Cut

open CategoryTheory.CoherentRealization.OriginalBeadInterval
open OriginalTwoBead.OrdinalCharts

/-- Reassembly reads back the SAME full original first-cut input. -/
theorem reassembly_left (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints) :
    concatLeft.{u} (leftData T j hj) (rightData T j hj) ≫ (nativeReassemblyIso T j hj).hom =
      leftMap T j hj := by
  change concatLeft.{u} (leftData T j hj) (rightData T j hj) ≫
    (reassemblyMorphism T j hj).map = leftMap T j hj
  apply (cancel_mono (complex.{u} T.joints).ι).1
  rw [Category.assoc, SSet.OriginalNecklace.Morphism.map_ι, ← Category.assoc,
    concatLeft_ι, Category.assoc, leftMap_ι, ← SSet.stdSimplex.map_comp]
  congr 1
  congr 1
  ext i : 3
  exact reassembly_prefix T j hj i

/-- Reassembly reads back the SAME full original second-cut input. -/
theorem reassembly_right (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints) :
    concatRight.{u} (leftData T j hj) (rightData T j hj) ≫ (nativeReassemblyIso T j hj).hom =
      rightMap T j hj := by
  change concatRight.{u} (leftData T j hj) (rightData T j hj) ≫
    (reassemblyMorphism T j hj).map = rightMap T j hj
  apply (cancel_mono (complex.{u} T.joints).ι).1
  rw [Category.assoc, SSet.OriginalNecklace.Morphism.map_ι, ← Category.assoc,
    concatRight_ι, Category.assoc, rightMap_ι, ← SSet.stdSimplex.map_comp]
  congr 1

/-- The SAME two original cut maps form the genuine pushout into the entire original necklace. -/
theorem isPushout (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints) :
    IsPushout ((leftData T j hj).target.{u}) (rightData T j hj).source
      (leftMap T j hj) (rightMap T j hj) := by
  apply (concat_isPushout (leftData T j hj) (rightData T j hj)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (nativeReassemblyIso T j hj)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simpa only [Iso.refl_hom, Category.id_comp] using reassembly_left T j hj
  · simpa only [Iso.refl_hom, Category.id_comp] using reassembly_right T j hj

/-- The SAME whole original input map is uniquely determined by both complete original cut maps. -/
theorem hom_ext (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints)
    {K : SSet.{u}} {f g : T.object ⟶ K}
    (hl : leftMap T j hj ≫ f = leftMap T j hj ≫ g)
    (hr : rightMap T j hj ≫ f = rightMap T j hj ≫ g) : f = g :=
  (isPushout T j hj).hom_ext hl hr

/-- The complete original cut gluing reads the SAME whole original input. -/
theorem desc_input (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints)
    {K : SSet.{u}} (f : T.object ⟶ K) :
    (isPushout T j hj).desc (leftMap T j hj ≫ f) (rightMap T j hj ≫ f)
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun h => h ≫ f) (cut_square T j hj)).trans (Category.assoc _ _ _))) = f := by
  apply hom_ext T j hj
  · exact (isPushout T j hj).inl_desc _ _ _
  · exact (isPushout T j hj).inr_desc _ _ _

end SSet.OriginalNecklace.Cut
