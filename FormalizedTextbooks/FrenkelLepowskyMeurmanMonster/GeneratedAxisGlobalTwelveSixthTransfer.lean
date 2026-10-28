/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthIdent
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootPairs
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSourceFiber
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialWords
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightPreparationMonomial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionCo1FrameOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionOmegaClass

/-! Partner transfers at the phase-merged Sixth cells.

A partner family's identification `sExtra^{±1} (h · v_k) = g · v₅` places one triality image of
`g · v₅` in the catalogue union. Every identification letter other than the source Xi fixes the
binary Ω class, so for `g = m · c` with an Xi-free prefix `m` and an odd-letter word `c` the
binary root of `g` is that of `c`. If a Sixth forest-letter word carries the root of a
phase-merged cell word to the root of `c`, the root pair relation transfers the membership to
the cell, and the phase merge gives the positive image. Hence one identification binds both
families. The partner identifications themselves are hypotheses here. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent
set_option backward.isDefEq.respectTransparency false

/-- Every genuine Golay sign isometry fixes the binary Ω class. -/
theorem sixthFrame_golaySign (d : golayCode) :
    QuotientGroup.mk' signsSubgroup (golaySignIsometry d) ∈ co1OmegaFrameStabilizer := by
  have hint : leechIntegralAction (golaySignIsometry d) (leechCoordinateFrameLattice 0) =
      leechCoordinateFrameLattice 0 ∨
      leechIntegralAction (golaySignIsometry d) (leechCoordinateFrameLattice 0) =
        -leechCoordinateFrameLattice 0 := by
    by_cases h0 : d.val 0 = 0
    · left
      apply Subtype.ext
      rw [leechIntegralAction_golaySign]
      funext i
      simp only [golayIntegerSign]
      split_ifs with hi
      · rfl
      · have hne : i ≠ 0 := fun h => hi (h ▸ h0)
        simp [leechCoordinateFrameLattice, leechCoordinateFrameVector, hne]
    · right
      apply Subtype.ext
      rw [leechIntegralAction_golaySign]
      funext i
      simp only [golayIntegerSign]
      split_ifs with hi
      · have hne : i ≠ 0 := fun h => h0 (h ▸ hi)
        simp [leechCoordinateFrameLattice, leechCoordinateFrameVector, hne]
      · rfl
  have hred : leechModTwoAction (golaySignIsometry d)
      (leechReduction (leechCoordinateFrameLattice 0)) =
      leechReduction (leechCoordinateFrameLattice 0) := by
    change leechQuotientAut (leechIntegralAction (golaySignIsometry d))
      (leechReduction (leechCoordinateFrameLattice 0)) = _
    rw [leechQuotientAut_reduce]
    rcases hint with h | h
    · rw [h]
    · rw [h, leechReduction_neg]
  change co1BinaryAction (QuotientGroup.mk' signsSubgroup (golaySignIsometry d))
    (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) = Multiplicative.toAdd (qQuotHom sourceOmegaQ)
  rw [sourceOmegaQ_eq_frame_class]
  change leechBinaryAction (golaySignIsometry d)
    (leechHyperbolicCoordinates (leechReduction (leechCoordinateFrameLattice 0))) = _
  rw [leechBinaryAction_coordinates, hred]

set_option maxRecDepth 100000 in
-- Evaluate the eight sign and permutation source letters on the Ω mask.
/-- The source sign and permutation letters fix the Ω mask. -/
theorem sixthFrame_oddRows : ∀ l : Fin 10, 2 ≤ l.val →
    generatedAxisGlobalMaskRowsAction (generatedAxisGlobalOddSourceRows l) 2048 = 2048 := by
  decide +kernel

/-- The source sign and permutation letters fix the binary Ω class. -/
theorem sixthFrame_oddLetter (l : Fin 10) (hl : 2 ≤ l.val) :
    projH (generatedAxisGlobalOddSourceLocalLetter l) ∈ co1OmegaFrameStabilizer := by
  change co1BinaryAction (projH (generatedAxisGlobalOddSourceLocalLetter l))
    (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) = Multiplicative.toAdd (qQuotHom sourceOmegaQ)
  rw [generatedAxisGlobalTwelveSixth_omega_mask, generatedAxisGlobalOddSourceLocalLetter_binary,
    sixthFrame_oddRows l hl]

/-- Every identification letter other than the source Xi fixes the binary Ω class. -/
theorem sixthFrame_identLetter (l : IdentLetter) (hl : l ≠ IdentLetter.xi) :
    projH (identWordLocal [l]) ∈ co1OmegaFrameStabilizer := by
  rw [identWordLocal_singleton]
  cases l with
  | xi => exact absurd rfl hl
  | sign a ε =>
    change projH (localFiberIntoH (generatedFifthSignFiber a ε)) ∈ co1OmegaFrameStabilizer
    rw [generatedFifth_sign_fiber_local, generatedFifth_sign_local_projection]
    exact sixthFrame_golaySign _
  | mono m =>
    obtain ⟨i, b⟩ := m
    fin_cases i <;> cases b
    · change projH (localFiberIntoH (generatedAxisGlobalOddSourceFiberLetter 6)) ∈
        co1OmegaFrameStabilizer
      rw [generatedAxisGlobalOddSourceFiberLetter_local]
      exact sixthFrame_oddLetter 6 (by decide)
    · change projH (localFiberIntoH (generatedAxisGlobalOddSourceFiberLetter 7)) ∈
        co1OmegaFrameStabilizer
      rw [generatedAxisGlobalOddSourceFiberLetter_local]
      exact sixthFrame_oddLetter 7 (by decide)
    · change projH (localFiberIntoH (generatedAxisGlobalOddSourceFiberLetter 8)) ∈
        co1OmegaFrameStabilizer
      rw [generatedAxisGlobalOddSourceFiberLetter_local]
      exact sixthFrame_oddLetter 8 (by decide)
    · change projH (localFiberIntoH (generatedAxisGlobalOddSourceFiberLetter 9)) ∈
        co1OmegaFrameStabilizer
      rw [generatedAxisGlobalOddSourceFiberLetter_local]
      exact sixthFrame_oddLetter 9 (by decide)
  | qel g =>
    change projH (inclQ g) ∈ co1OmegaFrameStabilizer
    rw [projH_inclQ]
    exact co1OmegaFrameStabilizer.one_mem

/-- Every Xi-free identification word fixes the binary Ω class. -/
theorem sixthFrame_identWord (ls : List IdentLetter) (hls : ∀ l ∈ ls, l ≠ IdentLetter.xi) :
    projH (identWordLocal ls) ∈ co1OmegaFrameStabilizer := by
  induction ls with
  | nil =>
    have h1 : identWordLocal [] = 1 := by simp [identWordLocal, identWordFiber]
    rw [h1, map_one]
    exact co1OmegaFrameStabilizer.one_mem
  | cons l ls ih =>
    rw [show l :: ls = [l] ++ ls from rfl, identWordLocal_append, map_mul]
    exact co1OmegaFrameStabilizer.mul_mem (sixthFrame_identLetter l (hls l (by simp)))
      (ih fun m hm => hls m (by simp [hm]))

/-- A frame-fixing left factor does not change the actual binary root. -/
theorem sixthFrame_binaryRoot (n r : H) (hn : projH n ∈ co1OmegaFrameStabilizer) :
    generatedAxisGlobalBinaryRoot (n * r) = generatedAxisGlobalBinaryRoot r := by
  apply Subtype.ext
  change co1BinaryAction (projH (n * r)⁻¹) (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) =
    co1BinaryAction (projH r⁻¹) (Multiplicative.toAdd (qQuotHom sourceOmegaQ))
  have hn' : co1BinaryAction (projH n⁻¹) (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) =
      Multiplicative.toAdd (qQuotHom sourceOmegaQ) := by
    have h1 := co1OmegaFrameStabilizer.inv_mem hn
    rw [← map_inv] at h1
    exact h1
  rw [mul_inv_rev, map_mul, map_mul, LinearEquiv.mul_apply, hn']

/-- A partner identification `sExtra (h · v_k) = g · v` puts `sExtra⁻¹ (g · v)` in the union. -/
theorem sixthPartner_inverse_mem (k : Fin 12) (h g : H) (v : GriessSpace)
    (he : sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative k)) = rhoLocal g v) :
    sExtra⁻¹ (rhoLocal g v) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [← he, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  exact ⟨k, h, rfl⟩

/-- A partner identification `sExtra⁻¹ (h · v_k) = g · v` puts `sExtra (g · v)` in the union. -/
theorem sixthPartner_forward_mem (k : Fin 12) (h g : H) (v : GriessSpace)
    (he : sExtra⁻¹ (rhoLocal h (generatedAxisGlobalTwelveRepresentative k)) = rhoLocal g v) :
    sExtra (rhoLocal g v) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [← he, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
  exact ⟨k, h, rfl⟩

/-- Transfer along a binary root match in the Sixth stabilizer: a triality image of `g · v₅`
in the union gives a triality image of the cell vector in the union. -/
theorem sixthCell_or_of_root_match (i : Fin 10) (g c : H)
    (hc : c ∈ generatedSixthLocalAxisStabilizer)
    (hroot : generatedAxisGlobalBinaryAct c (generatedAxisGlobalBinaryRoot (sixthCellWord i)) =
      generatedAxisGlobalBinaryRoot g)
    (hmem : sExtra (rhoLocal g generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∨
      sExtra⁻¹ (rhoLocal g generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal (sixthCellWord i) generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∨
      sExtra⁻¹ (rhoLocal (sixthCellWord i) generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have hfix : rhoLocal c generatedSixthAxis = generatedSixthAxis := hc
  rcases generatedAxisGlobalTwelve_root_relation_pair generatedSixthAxis g (sixthCellWord i) c
      hfix hroot with ⟨⟨k, hk⟩, ⟨k', hk'⟩⟩ | ⟨⟨k, hk⟩, ⟨k', hk'⟩⟩
  · rcases hmem with h | h
    · exact Or.inl (generatedAxisGlobalTwelve_union_mem_of_local _ k h hk)
    · exact Or.inr (generatedAxisGlobalTwelve_union_mem_of_local _ k' h hk')
  · rcases hmem with h | h
    · exact Or.inr (generatedAxisGlobalTwelve_union_mem_of_local _ k h hk)
    · exact Or.inl (generatedAxisGlobalTwelve_union_mem_of_local _ k' h hk')

/-- At a phase-merged Sixth cell, the transfer along a binary root match binds the positive
vector of the cell. -/
theorem sixthCell_pos_of_root_match (i : Fin 10)
    (hi : i ∈ ({3, 4, 5, 6, 7, 9} : Finset (Fin 10))) (g c : H)
    (hc : c ∈ generatedSixthLocalAxisStabilizer)
    (hroot : generatedAxisGlobalBinaryAct c (generatedAxisGlobalBinaryRoot (sixthCellWord i)) =
      generatedAxisGlobalBinaryRoot g)
    (hmem : sExtra (rhoLocal g generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∨
      sExtra⁻¹ (rhoLocal g generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal (sixthCellWord i) generatedSixthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rcases sixthCell_or_of_root_match i g c hc hroot hmem with h | h
  · exact h
  · obtain ⟨k0, hk0⟩ := sixthCell_phase_merge i hi
    rw [hk0]
    exact generatedLocalOrbitUnion_local _ k0 h

/-- The binary root match for a candidate odd-letter word behind an Xi-free identification
prefix, from a Sixth forest-letter word carrying the cell root to the candidate root. -/
theorem sixthCell_root_match_of_transport (i : Fin 10) (cand : List (Fin 10))
    (hcand : ∀ l ∈ cand, l.val < 2 ∨ 6 ≤ l.val) (u : List (Fin 15))
    (hu : cand.foldr (fun l x => generatedAxisGlobalMaskRowsAction
      (generatedAxisGlobalOddSourceRows l) x) (sixthBitsetWordApply u (sixthCellMask i)) = 2048)
    (M : List IdentLetter) (hM : ∀ l ∈ M, l ≠ IdentLetter.xi) :
    ∃ c : H, c ∈ generatedSixthLocalAxisStabilizer ∧
      generatedAxisGlobalBinaryAct c (generatedAxisGlobalBinaryRoot (sixthCellWord i)) =
        generatedAxisGlobalBinaryRoot (identWordLocal (M ++ cand.flatMap sixthOddIdent)) := by
  have hw : identWordLocal (M ++ cand.flatMap sixthOddIdent) =
      identWordLocal M * (cand.map generatedAxisGlobalOddSourceLocalLetter).prod := by
    rw [identWordLocal_append, sixthOddIdent_word cand hcand]
  have hmemP : sixthBitsetWord u ∈ generatedSixthProjectedAxisStabilizer := by
    apply Subgroup.list_prod_mem
    intro a ha
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp ha
    exact generatedAxisGlobalTwelveSixthGenerator_projected_mem g
  obtain ⟨c, hc⟩ := hmemP
  refine ⟨c.val, c.property, ?_⟩
  apply Subtype.ext
  rw [hw, sixthFrame_binaryRoot _ _ (sixthFrame_identWord M hM),
    generatedAxisGlobalTwelveOddLetterProduct_root cand _ hu]
  change co1BinaryAction (projH c.val) (generatedAxisGlobalBinaryRoot (sixthCellWord i)).val = _
  have hc' : projH c.val = sixthBitsetWord u := hc
  rw [hc', sixthCellWord_root, sixthBitsetWord_action]

/-- Partner pairs at the phase-merged Sixth cells, from the gtenth transporter records:
`0` = Sixth cell 3 ↔ Tenth root 62 (candidate coset word Sixo6), `1` = Sixth cell 4 ↔ Tenth
root 63 (candidate coset word Sixo8). -/
def sixthPartnerCell : Fin 2 → Fin 10 := ![3, 4]

/-- The candidate odd-letter coset words of the partner pairs (product order). -/
def sixthPartnerCand : Fin 2 → List (Fin 10) := ![[1, 9, 7, 7, 1, 7], [1, 9, 1, 6]]

/-- Sixth forest-letter words carrying the cell roots to the candidate roots. -/
def sixthPartnerTransport : Fin 2 → List (Fin 15) := ![[6, 1], [8, 7, 6, 0]]

set_option maxRecDepth 100000 in
-- Kernel check of the two partner binary transports.
/-- The partner transports carry the cell roots to the candidate roots. -/
theorem sixthPartner_certificate : ∀ p : Fin 2,
    (sixthPartnerCand p).foldr (fun l x => generatedAxisGlobalMaskRowsAction
      (generatedAxisGlobalOddSourceRows l) x)
      (sixthBitsetWordApply (sixthPartnerTransport p) (sixthCellMask (sixthPartnerCell p))) =
      2048 := by
  decide +kernel

/-- One partner identification binds the positive vector of the partner Sixth cell: if a triality
image of `identWordLocal (M ++ cand) · v₅` lies in the union, for any Xi-free prefix `M`. -/
theorem sixthCell_pos_of_partner (p : Fin 2) (M : List IdentLetter)
    (hM : ∀ l ∈ M, l ≠ IdentLetter.xi)
    (hmem : sExtra (rhoLocal (identWordLocal (M ++ (sixthPartnerCand p).flatMap sixthOddIdent))
          (generatedAxisGlobalTwelveRepresentative 5)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∨
      sExtra⁻¹ (rhoLocal (identWordLocal (M ++ (sixthPartnerCand p).flatMap sixthOddIdent))
          (generatedAxisGlobalTwelveRepresentative 5)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal (sixthCellWord (sixthPartnerCell p)) generatedSixthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨c, hc, hr⟩ := sixthCell_root_match_of_transport (sixthPartnerCell p)
    (sixthPartnerCand p) (by fin_cases p <;> decide) (sixthPartnerTransport p)
    (sixthPartner_certificate p) M hM
  exact sixthCell_pos_of_root_match _ (by fin_cases p <;> decide) _ c hc hr hmem

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
