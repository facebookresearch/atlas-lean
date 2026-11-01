/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentP0Checks

/-! # The partner identification `F0+` (Fifth coset 0 to Fourth)

The exact pairing `pairTriGMO` of the two representations of
`GeneratedAxisGlobalTwelveFourthIdentP0Checks` is evaluated in seven kernel evaluations (matrix
part; short part: pairs, packed octads, odd terms; odd-short-to-tensor part; packed tensor dot);
their sum is `128`, so the forward triality image of the Fifth coset image is the Fourth image
(`ident_forward_GMO`).  The partner record forms used by the Fourth assembly and by worker
`gfifth` follow. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The denominators of the two packed tensors. -/
theorem fourthP0_dens :
    tensorWordDenAll fourthP0H = 256 ∧ tensorWordDenAll fourthP0G = 32 := by
  decide

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing. -/
theorem fourthP0_pmat : triMatF true fourthP0L fourthP0W = 29 / 8 := by
  decide +kernel

/-- The short scales of the two representations. -/
theorem fourthP0_sdens : fourthP0L.sden = 1 / 16 ∧ fourthP0W.sden = 1 / 8 := ⟨rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- The octad terms of the source representation fit the packed octad transform. -/
theorem fourthP0_octok : octPackOk 32 fourthP0L = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair terms of the short part of the pairing. -/
theorem fourthP0_pspairs :
    (fourthP0W.sh.pairs.map (fun q => (q.2 : ℚ) * triPairF true fourthP0L q.1)).sum =
      9 / 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad terms of the short part of the pairing (packed octad Fourier, integer form). -/
theorem fourthP0_psoct :
    (fourthP0W.sh.oct.map (fun b => (b.2.map (fun q =>
      q.2 * octZ 32 true (octPackX 32 true fourthP0L) b.1 q.1)).sum)).sum = 32576 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of the short part of the pairing. -/
theorem fourthP0_psodd :
    (fourthP0W.sh.odd.map (fun q => (q.2 : ℚ) * triOddF true fourthP0L q.1)).sum =
      288 := by
  decide +kernel

/-- The short part of the pairing (packed octad Fourier). -/
theorem fourthP0_pshort : triShortO 32 true fourthP0L fourthP0W = 547 / 8 := by
  rw [triShortO]
  simp only [fourthP0_octok, ↓reduceIte]
  rw [fourthP0_pspairs, fourthP0_psoct, fourthP0_psodd, fourthP0_sdens.1, fourthP0_sdens.2]
  norm_num

set_option maxRecDepth 100000 in
/-- The odd-short-to-tensor part of the pairing. -/
theorem fourthP0_podd :
    (fourthP0L.sh.odd.map (fun q =>
      fourthP0L.sden * (q.2 : ℚ) * triTCF true fourthP0W q.1)).sum = 56 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The packed tensor dot product of the pairing. -/
theorem fourthP0_ptdot :
    tdotM 64 (trialityTensorT 64 false fourthP0HX) fourthP0GX = 917504 := by
  decide +kernel

/-- The exact pairing of the two representations is `128`. -/
theorem fourthP0_pair : pairTriGMO 32 64 true fourthP0L fourthP0W fourthP0HX fourthP0GX
    ((tensorWordDenAll fourthP0H : ℚ) * 1) ((tensorWordDenAll fourthP0G : ℚ) * 1) = 128 := by
  unfold pairTriGMO
  rw [fourthP0_pmat, fourthP0_pshort, fourthP0_podd, show (!true) = false from rfl]
  rw [fourthP0_ptdot, fourthP0_dens.1, fourthP0_dens.2]
  norm_num

/-- The partner identification `F0+`. -/
theorem fourthP0_ident : sExtra (rhoLocal (identWordLocal fourthP0H)
    (generatedAxisGlobalTwelveRepresentative 4)) =
      rhoLocal (identWordLocal fourthP0G) (generatedAxisGlobalTwelveRepresentative 3) := by
  have hX := (tensorWordAll_actual fourthP0H (fifthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [fourthP0H_growth]; norm_num) 1).1
  have hY := (tensorWordAll_actual fourthP0G (fourthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [fourthP0G_growth]; norm_num) 1).1
  rw [fourthP0H_growth] at hX
  rw [fourthP0G_growth] at hY
  exact ident_forward_GMO 4 3 _ _ fourthP0L fourthP0W
    (ofList_ok fourthP0HT fourthP0T_labels.1) (ofList_ok fourthP0GT fourthP0T_labels.2) rfl rfl
    hX hY (by norm_num) (by norm_num) fourthP0L_actual fourthP0W_actual fourthP0_pair

/-- The prefix of the target word is Xi-free. -/
theorem fourth_prefix_noXi_P0 :
    ∀ l ∈ ([.qel (qmElt (9327376, true)), .sign 4 0] : List IdentLetter), l ≠ IdentLetter.xi := by
  intro l hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl <;> exact fun h => IdentLetter.noConfusion h

/-- The target word is the frame-fixing prefix times the translated Fourth source word. -/
theorem fourthP0G_eq :
    fourthP0G = [.qel (qmElt (9327376, true)), .sign 4 0] ++ fourthSourceWord (fourthPartnerWord 0) := rfl

set_option maxRecDepth 100000 in
/-- The partner record of `F0+` in the form used by the Fourth assembly. -/
theorem fourthP0_partner :
    ∃ n : List IdentLetter, (∀ l ∈ n, l ≠ IdentLetter.xi) ∧ ∃ i : Fin 12,
      FourthPartner n (fourthPartnerWord 0) (generatedAxisGlobalTwelveRepresentative i) := by
  refine ⟨[.qel (qmElt (9327376, true)), .sign 4 0], fourth_prefix_noXi_P0, 4,
    identWordLocal fourthP0H, Or.inl ?_⟩
  rw [← fourthP0G_eq]
  exact fourthP0_ident

set_option maxRecDepth 100000 in
/-- The partner record of `F0+` in the form used by worker `gfifth`. -/
theorem fourthP0_fifth : ∃ g : H, sExtra (rhoLocal (identWordLocal
    (generatedAxisGlobalTwelveFifthBindCosetLetters 0))
      (generatedAxisGlobalTwelveRepresentative 4)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative 3) :=
  ⟨_, fourthP0_ident⟩

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
