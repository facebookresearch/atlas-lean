/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentAssemblyFifth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR6p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR7p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR9p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR10p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR14p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR14n
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR820p

/-! # Fourth-family coverage with the Sixth, Seventh, Eighth and Root-eight identifications

The partner-facing identifications at the translated root words of roots `6, 7, 14` (Seventh),
`9` (Eighth), `10` and the inverse one at root `14` (Sixth) are proved
(`GeneratedAxisGlobalTwelveFourthIdentR*`).  Root `4` is bound by worker `r8f`'s identification
`wR8fR820p_ident` (Root-eight image onto a Fourth image): its Fourth-side word is a Xi-free prefix
times the translated root word of root `4`, so it is a partner record of the merged root `4`
(`fourth_root4_bound`).  What remains for the coverage of the Fourth family: the forward
identification at root `3` (Twelfth), the two Tenth partner records (`p5`, `p8`) and the Odd
classes of the forward image at root twelve and of the inverse image at root fifteen.  These
remain hypotheses here; no family coverage is assumed. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The letters other than the Xi letter. -/
def identNotXi : IdentLetter → Bool
  | .xi => false
  | _ => true

/-- A word all of whose letters pass `identNotXi` is Xi-free. -/
theorem ne_xi_of_all {n : List IdentLetter} (h : n.all identNotXi = true) :
    ∀ l ∈ n, l ≠ IdentLetter.xi := by
  intro l hl hx
  rw [List.all_eq_true] at h
  have := h l hl
  rw [hx] at this
  exact absurd this (by decide)

/-- The Xi-free prefix of the Fourth-side word of the identification `wR8fR820p_ident`. -/
def fourthR4N : List IdentLetter :=
  [.qel (qmElt (14509896, false)), .sign 372 0,
    .mono (0, false), .mono (1, false), .mono (0, true), .mono (0, true), .mono (0, true),
    .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true),
    .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, true), .mono (0, true),
    .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, false),
    .mono (0, false), .mono (1, false), .mono (0, true), .mono (1, false)]

/-- The prefix is Xi-free. -/
theorem fourthR4N_noXi : ∀ l ∈ fourthR4N, l ≠ IdentLetter.xi :=
  ne_xi_of_all (by decide)

set_option maxRecDepth 100000 in
/-- The Fourth-side word of `wR8fR820p_ident` is the prefix times the translated root word of
root `4`. -/
theorem fourthR4G_eq :
    wR8fR820pG = fourthR4N ++ fourthSourceWord (generatedAxisGlobalTwelveFourthRootWords 4) := rfl

set_option maxRecDepth 100000 in
/-- The translated root word of root `4` carries its binary root mask to the base mask. -/
theorem fourthR4_mask : (generatedAxisGlobalTwelveFourthRootWords 4).foldr (fun l x =>
    generatedAxisGlobalMaskRowsAction (generatedAxisGlobalOddSourceRows l) x)
      (generatedAxisGlobalTwelveFourthRootMask (generatedAxisGlobalTwelveFourthMergedRoot 3)) =
      2048 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Root `4` of the Fourth forest: both triality images lie in the twelve local orbits, by the
Root-eight identification `wR8fR820p_ident` (worker `r8f`). -/
theorem fourth_root4_bound :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal
        (generatedAxisGlobalTwelveFourthMergedRoot 3)) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal
        (generatedAxisGlobalTwelveFourthMergedRoot 3)) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  fourth_partner_merged 3 fourthR4N fourthR4N_noXi (generatedAxisGlobalTwelveFourthRootWords 4) _
    fourthR4_mask [] rfl 9
    ⟨identWordLocal wR8fR820pH, Or.inl (by rw [← fourthR4G_eq]; exact wR8fR820p_ident)⟩

set_option maxRecDepth 100000 in
/-- Fourth-family coverage from the Twelfth identification at root `3`, the two Tenth partner
records and the two Odd classes; every other root image is bound by a proved identification. -/
theorem generatedAxisGlobalTwelve_fourth_covered_of_remaining
    (h3 : FourthIdentForward (generatedAxisGlobalTwelveFourthRootWords 3))
    (p5 : ∃ n : List IdentLetter, (∀ l ∈ n, l ≠ IdentLetter.xi) ∧ ∃ i : Fin 12,
      FourthPartner n (fourthPartnerWord 2) (generatedAxisGlobalTwelveRepresentative i))
    (p8 : ∃ n : List IdentLetter, (∀ l ∈ n, l ≠ IdentLetter.xi) ∧ ∃ i : Fin 12,
      FourthPartner n (fourthPartnerWord 3) (generatedAxisGlobalTwelveRepresentative i))
    (hodd12 : sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 12) generatedFourthAxis) ∈
      MulAction.orbit H generatedOddAxis)
    (hodd15 : sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 15)
      generatedFourthAxis) ∈ MulAction.orbit H generatedOddAxis) :
    GeneratedAxisGlobalTwelveFamilyCovered 3 := by
  have hodd_mem : ∀ {x : GriessSpace}, x ∈ MulAction.orbit H generatedOddAxis →
      x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
    fun hx => fourth_mem_union_of_orbit (k := 2) hx
  obtain ⟨n0, hn0, i0, q0⟩ := fourthP0_partner
  obtain ⟨n1, hn1, q1⟩ := fourthP12_partner
  obtain ⟨n5, hn5, i5, q5⟩ := p5
  obtain ⟨n8, hn8, i8, q8⟩ := p8
  have c0 := fourthPartner_certificate 0
  have c1 := fourthPartner_certificate 1
  have c5 := fourthPartner_certificate 2
  have c8 := fourthPartner_certificate 3
  have r0 := fourth_partner_merged 0 n0 hn0 _ _ c0.1 _ c0.2 i0 q0
  have r5 := fourth_partner_merged 4 n5 hn5 _ _ c5.1 _ c5.2 i5 q5
  have r8 := fourth_partner_merged 7 n8 hn8 _ _ c8.1 _ c8.2 i8 q8
  have r1 := generatedAxisGlobalTwelveFourth_root1_of_classes
    (fourth_root1_fourth_of_ident fourthF1_self)
    (fourth_partner_orbit 1 n1 hn1 _ _ c1.1 _ c1.2 _ q1)
  have r2 := fourth_root2_of_ident fourthF2_inverse
  have r13 := fourth_root13_of_ident fourthF13_inverse
  have r3 := fourth_merged_forward 2 h3
  have r4 := fourth_root4_bound
  have r6 := fourth_merged_forward 5 fourthR6p_forward
  have r7 := fourth_merged_forward 6 fourthR7p_forward
  have r9 := fourth_merged_forward 8 fourthR9p_forward
  have r10 := fourth_merged_forward 9 fourthR10p_forward
  have r14p := fourth_root_forward 14 fourthR14p_forward
  have r14n := fourth_root_inverse 14 fourthR14n_inverse
  have r12n := generatedAxisGlobalTwelveFourth_root12_of_classes
    (fourth_root12_fourth_of_ident fourthF12_self) hodd12
  have r15p := fourth_root15_of_ident fourthF15_self hodd15
  apply generatedAxisGlobalTwelve_fourth_covered_of_open
  · intro i hi
    simp only [generatedAxisGlobalTwelveFourthOpenPositive, Finset.mem_insert,
      Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · exact r0.1
    · exact r1.1
    · exact r2.1
    · exact r3.1
    · exact r4.1
    · exact r5.1
    · exact r6.1
    · exact r7.1
    · exact r8.1
    · exact r9.1
    · exact r10.1
    · exact hodd_mem hodd12
    · exact r13.1
    · exact r14p
    · exact r15p
  · intro i hi
    simp only [generatedAxisGlobalTwelveFourthOpenNegative, Finset.mem_insert,
      Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact r1.2
    · exact r12n
    · exact r14n
    · exact hodd_mem hodd15

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
