/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthTriangle

/-! Partner triangles at the Sixth and Seventh cells.

If a partner family has both triality images of one of its vectors `x` in the catalogue union,
the triangle of `x` has all its vertices bound. When one vertex is `(M ++ c) · v` with an
Xi-free prefix `M` and an odd-letter word `c` whose binary root lies in the stabilizer orbit of
the root of a Sixth or Seventh cell word, the root pair relation transfers both images to the
cell word, whatever the phase and also at cells without phase merge. So the two identifications
a partner needs for its own vector also bind the gforest cell; no gforest identification is
needed for such a cell. The partner identifications are hypotheses here. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent
set_option backward.isDefEq.respectTransparency false

/-- Partner triangle at a Sixth cell, from a forest-letter certificate for the candidate word. -/
theorem sixthCell_both_of_triangle (i : Fin 10) (cand : List (Fin 10))
    (hcand : ∀ l ∈ cand, l.val < 2 ∨ 6 ≤ l.val) (u : List (Fin 15))
    (hu : cand.foldr (fun l x => generatedAxisGlobalMaskRowsAction
      (generatedAxisGlobalOddSourceRows l) x) (sixthBitsetWordApply u (sixthCellMask i)) = 2048)
    (M : List IdentLetter) (hM : ∀ l ∈ M, l ≠ IdentLetter.xi) (x : GriessSpace)
    (hx : x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hp : sExtra x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hm : sExtra⁻¹ x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hz : sExtra x = rhoLocal (identWordLocal (M ++ cand.flatMap sixthOddIdent))
        (generatedAxisGlobalTwelveRepresentative 5) ∨
      sExtra⁻¹ x = rhoLocal (identWordLocal (M ++ cand.flatMap sixthOddIdent))
        (generatedAxisGlobalTwelveRepresentative 5)) :
    sExtra (rhoLocal (sixthCellWord i) generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (sixthCellWord i) generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨c, hc, hr⟩ := sixthCell_root_match_of_transport i cand hcand u hu M hM
  have hzb := sixthTri_vertex_both _ x _ hx hp hm (hz.imp Eq.symm Eq.symm)
  exact generatedAxisGlobalTwelve_root_pair_mem _ generatedSixthAxis _ (sixthCellWord i) c hc hr
    hzb.1 hzb.2

/-- Partner triangle at a Seventh cell, from a forest-letter certificate for the candidate word. -/
theorem seventhCell_both_of_triangle (i : Fin 23) (cand : List (Fin 10))
    (hcand : ∀ l ∈ cand, l.val < 2 ∨ 6 ≤ l.val) (u : List (Fin 4))
    (hu : cand.foldr (fun l x => generatedAxisGlobalMaskRowsAction
      (generatedAxisGlobalOddSourceRows l) x) (seventhBitsetWordApply u (seventhCellMask i)) =
        2048)
    (M : List IdentLetter) (hM : ∀ l ∈ M, l ≠ IdentLetter.xi) (x : GriessSpace)
    (hx : x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hp : sExtra x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hm : sExtra⁻¹ x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hz : sExtra x = rhoLocal (identWordLocal (M ++ cand.flatMap sixthOddIdent))
        (generatedAxisGlobalTwelveRepresentative 6) ∨
      sExtra⁻¹ x = rhoLocal (identWordLocal (M ++ cand.flatMap sixthOddIdent))
        (generatedAxisGlobalTwelveRepresentative 6)) :
    sExtra (rhoLocal (seventhCellWord i) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (seventhCellWord i) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨c, hc, hr⟩ := seventhCell_root_match_of_transport i cand hcand u hu M hM
  have hzb := sixthTri_vertex_both _ x _ hx hp hm (hz.imp Eq.symm Eq.symm)
  exact generatedAxisGlobalTwelve_root_pair_mem _ generatedSeventhAxis _ (seventhCellWord i) c hc
    hr hzb.1 hzb.2

/-- The gtenth partner triangles at the Sixth cells `3, 4` (Tenth roots 62, 63). -/
theorem sixthCell_both_of_partner (p : Fin 2) (M : List IdentLetter)
    (hM : ∀ l ∈ M, l ≠ IdentLetter.xi) (x : GriessSpace)
    (hx : x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hp : sExtra x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hm : sExtra⁻¹ x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hz : sExtra x = rhoLocal (identWordLocal (M ++ (sixthPartnerCand p).flatMap sixthOddIdent))
        (generatedAxisGlobalTwelveRepresentative 5) ∨
      sExtra⁻¹ x = rhoLocal (identWordLocal (M ++ (sixthPartnerCand p).flatMap sixthOddIdent))
        (generatedAxisGlobalTwelveRepresentative 5)) :
    sExtra (rhoLocal (sixthCellWord (sixthPartnerCell p)) generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (sixthCellWord (sixthPartnerCell p)) generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  sixthCell_both_of_triangle _ _ (by fin_cases p <;> decide) _ (sixthPartner_certificate p) M hM
    x hx hp hm hz

/-- The gtenth partner triangles at the Seventh cells `4, 5, 15, 11, 12, 17` (Tenth roots 29,
57, 54, 51, 56, 50): both images, also at the cells without phase merge. -/
theorem seventhCell_both_of_partner (p : Fin 6) (M : List IdentLetter)
    (hM : ∀ l ∈ M, l ≠ IdentLetter.xi) (x : GriessSpace)
    (hx : x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hp : sExtra x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hm : sExtra⁻¹ x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hz : sExtra x = rhoLocal (identWordLocal (M ++ (seventhPartnerCand p).flatMap sixthOddIdent))
        (generatedAxisGlobalTwelveRepresentative 6) ∨
      sExtra⁻¹ x = rhoLocal (identWordLocal (M ++ (seventhPartnerCand p).flatMap sixthOddIdent))
        (generatedAxisGlobalTwelveRepresentative 6)) :
    sExtra (rhoLocal (seventhCellWord (seventhPartnerCell p)) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (seventhCellWord (seventhPartnerCell p)) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  seventhCell_both_of_triangle _ _ (by fin_cases p <;> decide) _ (seventhPartner_certificate p) M
    hM x hx hp hm hz

/-- At the exact cell word (empty transport) a partner triangle binds both images of the cell. -/
theorem sixthCell_both_of_cell_triangle (i : Fin 10) (M : List IdentLetter)
    (hM : ∀ l ∈ M, l ≠ IdentLetter.xi) (x : GriessSpace)
    (hx : x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hp : sExtra x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hm : sExtra⁻¹ x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hz : sExtra x = rhoLocal (identWordLocal (M ++ sixthCellIdent i))
        (generatedAxisGlobalTwelveRepresentative 5) ∨
      sExtra⁻¹ x = rhoLocal (identWordLocal (M ++ sixthCellIdent i))
        (generatedAxisGlobalTwelveRepresentative 5)) :
    sExtra (rhoLocal (sixthCellWord i) generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (sixthCellWord i) generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [sixthCellWord_ident]
  exact sixthTri_target_both x M _ hM _ hx hp hm hz

/-- At the exact cell word (empty transport) a partner triangle binds both images of the cell. -/
theorem seventhCell_both_of_cell_triangle (i : Fin 23) (M : List IdentLetter)
    (hM : ∀ l ∈ M, l ≠ IdentLetter.xi) (x : GriessSpace)
    (hx : x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hp : sExtra x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hm : sExtra⁻¹ x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hz : sExtra x = rhoLocal (identWordLocal (M ++ seventhCellIdent i))
        (generatedAxisGlobalTwelveRepresentative 6) ∨
      sExtra⁻¹ x = rhoLocal (identWordLocal (M ++ seventhCellIdent i))
        (generatedAxisGlobalTwelveRepresentative 6)) :
    sExtra (rhoLocal (seventhCellWord i) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (seventhCellWord i) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [seventhCellWord_ident]
  exact sixthTri_target_both x M _ hM _ hx hp hm hz

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
