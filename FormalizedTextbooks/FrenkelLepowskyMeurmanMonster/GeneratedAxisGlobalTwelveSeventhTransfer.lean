/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdent
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthTransfer

/-! Partner transfers at the Seventh cells.

As for the Sixth family: a partner identification `sExtra^{±1} (h · v_k) = g · v₆` with
`g = m · c` (Xi-free prefix `m`, odd-letter word `c`) places a triality image of `g · v₆` in the
catalogue union; a Seventh forest-letter word carrying a cell root to the root of `c` transfers
it to one triality image of the cell vector, which at a phase-merged cell gives the positive
image. At a cell without phase merge only the disjunction is transferred. The partner
identifications themselves are hypotheses here. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent
set_option backward.isDefEq.respectTransparency false

/-- Transfer along a binary root match in the Seventh stabilizer: a triality image of `g · v₆`
in the union gives a triality image of the cell vector in the union. -/
theorem seventhCell_or_of_root_match (i : Fin 23) (g c : H)
    (hc : c ∈ generatedSeventhLocalAxisStabilizer)
    (hroot : generatedAxisGlobalBinaryAct c (generatedAxisGlobalBinaryRoot (seventhCellWord i)) =
      generatedAxisGlobalBinaryRoot g)
    (hmem : sExtra (rhoLocal g generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∨
      sExtra⁻¹ (rhoLocal g generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal (seventhCellWord i) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∨
      sExtra⁻¹ (rhoLocal (seventhCellWord i) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have hfix : rhoLocal c generatedSeventhAxis = generatedSeventhAxis := hc
  rcases generatedAxisGlobalTwelve_root_relation_pair generatedSeventhAxis g (seventhCellWord i) c
      hfix hroot with ⟨⟨k, hk⟩, ⟨k', hk'⟩⟩ | ⟨⟨k, hk⟩, ⟨k', hk'⟩⟩
  · rcases hmem with h | h
    · exact Or.inl (generatedAxisGlobalTwelve_union_mem_of_local _ k h hk)
    · exact Or.inr (generatedAxisGlobalTwelve_union_mem_of_local _ k' h hk')
  · rcases hmem with h | h
    · exact Or.inr (generatedAxisGlobalTwelve_union_mem_of_local _ k h hk)
    · exact Or.inl (generatedAxisGlobalTwelve_union_mem_of_local _ k' h hk')

/-- At a phase-merged Seventh cell, the transfer along a binary root match binds the positive
vector of the cell. -/
theorem seventhCell_pos_of_root_match (i : Fin 23)
    (hi : i ∈ ({4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 19} : Finset (Fin 23))) (g c : H)
    (hc : c ∈ generatedSeventhLocalAxisStabilizer)
    (hroot : generatedAxisGlobalBinaryAct c (generatedAxisGlobalBinaryRoot (seventhCellWord i)) =
      generatedAxisGlobalBinaryRoot g)
    (hmem : sExtra (rhoLocal g generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∨
      sExtra⁻¹ (rhoLocal g generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal (seventhCellWord i) generatedSeventhAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rcases seventhCell_or_of_root_match i g c hc hroot hmem with h | h
  · exact h
  · obtain ⟨k0, hk0⟩ := seventhCell_phase_merge i hi
    rw [hk0]
    exact generatedLocalOrbitUnion_local _ k0 h

/-- The binary root match for a candidate odd-letter word behind an Xi-free identification
prefix, from a Seventh forest-letter word carrying the cell root to the candidate root. -/
theorem seventhCell_root_match_of_transport (i : Fin 23) (cand : List (Fin 10))
    (hcand : ∀ l ∈ cand, l.val < 2 ∨ 6 ≤ l.val) (u : List (Fin 4))
    (hu : cand.foldr (fun l x => generatedAxisGlobalMaskRowsAction
      (generatedAxisGlobalOddSourceRows l) x) (seventhBitsetWordApply u (seventhCellMask i)) =
        2048)
    (M : List IdentLetter) (hM : ∀ l ∈ M, l ≠ IdentLetter.xi) :
    ∃ c : H, c ∈ generatedSeventhLocalAxisStabilizer ∧
      generatedAxisGlobalBinaryAct c (generatedAxisGlobalBinaryRoot (seventhCellWord i)) =
        generatedAxisGlobalBinaryRoot (identWordLocal (M ++ cand.flatMap sixthOddIdent)) := by
  have hw : identWordLocal (M ++ cand.flatMap sixthOddIdent) =
      identWordLocal M * (cand.map generatedAxisGlobalOddSourceLocalLetter).prod := by
    rw [identWordLocal_append, sixthOddIdent_word cand hcand]
  have hmemP : seventhBitsetWord u ∈ generatedSeventhProjectedAxisStabilizer := by
    apply Subgroup.list_prod_mem
    intro a ha
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp ha
    exact seventhForestLetter_mem g
  obtain ⟨c, hc⟩ := hmemP
  refine ⟨c.val, c.property, ?_⟩
  apply Subtype.ext
  rw [hw, sixthFrame_binaryRoot _ _ (sixthFrame_identWord M hM),
    generatedAxisGlobalTwelveOddLetterProduct_root cand _ hu]
  change co1BinaryAction (projH c.val) (generatedAxisGlobalBinaryRoot (seventhCellWord i)).val = _
  have hc' : projH c.val = seventhBitsetWord u := hc
  rw [hc', seventhCellWord_root, seventhBitsetWord_action]

/-- Partner pairs at the Seventh cells, from the gtenth transporter records (Tenth root, candidate
coset word): `0` = cell 4 (root 29, Sevo9), `1` = cell 5 (root 57, Sevo10), `2` = cell 15
(root 54, Sevo23) are phase merged; `3` = cell 11 (root 51, Sevo18), `4` = cell 12 (root 56,
Sevo19), `5` = cell 17 (root 50, Sevo26) are not. -/
def seventhPartnerCell : Fin 6 → Fin 23 := ![4, 5, 15, 11, 12, 17]

/-- The candidate odd-letter coset words of the partner pairs (product order). -/
def seventhPartnerCand : Fin 6 → List (Fin 10) :=
  ![[1, 7, 9, 1, 6], [1, 9, 0, 7], [1, 7, 1, 9, 7, 9], [1, 9, 7, 1, 9], [1, 7, 1, 9],
    [1, 7, 9, 1, 9]]

/-- Seventh forest-letter words carrying the cell roots to the candidate roots. -/
def seventhPartnerTransport : Fin 6 → List (Fin 4) :=
  ![[2, 3, 0, 0, 3, 1, 0, 0, 1, 3], [0, 0, 2, 1, 2, 0, 0], [0, 3, 3, 1, 0, 2, 1, 3, 0, 0, 2],
    [3, 3, 2, 3, 1, 2, 0, 0, 0, 1], [0, 2, 0, 2, 1, 3, 3, 2, 3, 0],
    [0, 3, 0, 0, 0, 2, 3, 3, 2, 0, 0]]

set_option maxRecDepth 100000 in
-- Kernel check of the six partner binary transports.
/-- The partner transports carry the cell roots to the candidate roots. -/
theorem seventhPartner_certificate : ∀ p : Fin 6,
    (seventhPartnerCand p).foldr (fun l x => generatedAxisGlobalMaskRowsAction
      (generatedAxisGlobalOddSourceRows l) x)
      (seventhBitsetWordApply (seventhPartnerTransport p)
        (seventhCellMask (seventhPartnerCell p))) = 2048 := by
  decide +kernel

/-- One partner identification binds one triality image of the partner Seventh cell vector: if a
triality image of `identWordLocal (M ++ cand) · v₆` lies in the union, for any Xi-free prefix
`M`. -/
theorem seventhCell_or_of_partner (p : Fin 6) (M : List IdentLetter)
    (hM : ∀ l ∈ M, l ≠ IdentLetter.xi)
    (hmem : sExtra (rhoLocal (identWordLocal (M ++ (seventhPartnerCand p).flatMap sixthOddIdent))
          (generatedAxisGlobalTwelveRepresentative 6)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∨
      sExtra⁻¹ (rhoLocal (identWordLocal (M ++ (seventhPartnerCand p).flatMap sixthOddIdent))
          (generatedAxisGlobalTwelveRepresentative 6)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal (seventhCellWord (seventhPartnerCell p)) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∨
      sExtra⁻¹ (rhoLocal (seventhCellWord (seventhPartnerCell p)) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨c, hc, hr⟩ := seventhCell_root_match_of_transport (seventhPartnerCell p)
    (seventhPartnerCand p) (by fin_cases p <;> decide) (seventhPartnerTransport p)
    (seventhPartner_certificate p) M hM
  exact seventhCell_or_of_root_match _ _ c hc hr hmem

/-- At the phase-merged partner cells (`p < 3`) one partner identification binds the positive
vector of the Seventh cell. -/
theorem seventhCell_pos_of_partner (p : Fin 6) (hp : p.val < 3) (M : List IdentLetter)
    (hM : ∀ l ∈ M, l ≠ IdentLetter.xi)
    (hmem : sExtra (rhoLocal (identWordLocal (M ++ (seventhPartnerCand p).flatMap sixthOddIdent))
          (generatedAxisGlobalTwelveRepresentative 6)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∨
      sExtra⁻¹ (rhoLocal (identWordLocal (M ++ (seventhPartnerCand p).flatMap sixthOddIdent))
          (generatedAxisGlobalTwelveRepresentative 6)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal (seventhCellWord (seventhPartnerCell p)) generatedSeventhAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨c, hc, hr⟩ := seventhCell_root_match_of_transport (seventhPartnerCell p)
    (seventhPartnerCand p) (by fin_cases p <;> decide) (seventhPartnerTransport p)
    (seventhPartner_certificate p) M hM
  have hi : seventhPartnerCell p ∈
      ({4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 19} : Finset (Fin 23)) := by
    fin_cases p <;> simp_all [seventhPartnerCell]
  exact seventhCell_pos_of_root_match _ hi _ c hc hr hmem

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
