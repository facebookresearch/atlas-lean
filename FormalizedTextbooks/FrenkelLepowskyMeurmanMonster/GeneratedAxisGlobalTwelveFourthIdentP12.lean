/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentP12Checks

/-! # The partner identification `F12+` (Fifth coset 3 to Fourth)

The exact pairing `pairTriGMO` of the two representations of
`GeneratedAxisGlobalTwelveFourthIdentP12Checks` is evaluated in seven kernel evaluations (matrix
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
theorem fourthP12_dens :
    tensorWordDenAll fourthP12H = 256 ∧ tensorWordDenAll fourthP12G = 32 := by
  decide

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing. -/
theorem fourthP12_pmat : triMatF true fourthP12L fourthP12W = 29 / 8 := by
  decide +kernel

/-- The short scales of the two representations. -/
theorem fourthP12_sdens : fourthP12L.sden = 1 / 16 ∧ fourthP12W.sden = 1 / 8 := ⟨rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- The octad terms of the source representation fit the packed octad transform. -/
theorem fourthP12_octok : octPackOk 32 fourthP12L = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair terms of the short part of the pairing. -/
theorem fourthP12_pspairs :
    (fourthP12W.sh.pairs.map (fun q => (q.2 : ℚ) * triPairF true fourthP12L q.1)).sum =
      9 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad terms of the short part of the pairing (packed octad Fourier, integer form). -/
theorem fourthP12_psoct :
    (fourthP12W.sh.oct.map (fun b => (b.2.map (fun q =>
      q.2 * octZ 32 true (octPackX 32 true fourthP12L) b.1 q.1)).sum)).sum = 36096 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of the short part of the pairing. -/
theorem fourthP12_psodd :
    (fourthP12W.sh.odd.map (fun q => (q.2 : ℚ) * triOddF true fourthP12L q.1)).sum =
      256 := by
  decide +kernel

/-- The short part of the pairing (packed octad Fourier). -/
theorem fourthP12_pshort : triShortO 32 true fourthP12L fourthP12W = 547 / 8 := by
  rw [triShortO]
  simp only [fourthP12_octok, ↓reduceIte]
  rw [fourthP12_pspairs, fourthP12_psoct, fourthP12_psodd, fourthP12_sdens.1, fourthP12_sdens.2]
  norm_num

set_option maxRecDepth 100000 in
/-- The odd-short-to-tensor part of the pairing. -/
theorem fourthP12_podd :
    (fourthP12L.sh.odd.map (fun q =>
      fourthP12L.sden * (q.2 : ℚ) * triTCF true fourthP12W q.1)).sum = 48 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The packed tensor dot product of the pairing. -/
theorem fourthP12_ptdot :
    tdotM 64 (trialityTensorT 64 false fourthP12HX) fourthP12GX = 1048576 := by
  decide +kernel

/-- The exact pairing of the two representations is `128`. -/
theorem fourthP12_pair : pairTriGMO 32 64 true fourthP12L fourthP12W fourthP12HX fourthP12GX
    ((tensorWordDenAll fourthP12H : ℚ) * 1) ((tensorWordDenAll fourthP12G : ℚ) * 1) = 128 := by
  unfold pairTriGMO
  rw [fourthP12_pmat, fourthP12_pshort, fourthP12_podd, show (!true) = false from rfl]
  rw [fourthP12_ptdot, fourthP12_dens.1, fourthP12_dens.2]
  norm_num

/-- The partner identification `F12+`. -/
theorem fourthP12_ident : sExtra (rhoLocal (identWordLocal fourthP12H)
    (generatedAxisGlobalTwelveRepresentative 4)) =
      rhoLocal (identWordLocal fourthP12G) (generatedAxisGlobalTwelveRepresentative 3) := by
  have hX := (tensorWordAll_actual fourthP12H (fifthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [fourthP12H_growth]; norm_num) 1).1
  have hY := (tensorWordAll_actual fourthP12G (fourthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [fourthP12G_growth]; norm_num) 1).1
  rw [fourthP12H_growth] at hX
  rw [fourthP12G_growth] at hY
  exact ident_forward_GMO 4 3 _ _ fourthP12L fourthP12W
    (ofList_ok fourthP12HT fourthP12T_labels.1) (ofList_ok fourthP12GT fourthP12T_labels.2) rfl rfl
    hX hY (by norm_num) (by norm_num) fourthP12L_actual fourthP12W_actual fourthP12_pair

/-- The prefix of the target word is Xi-free. -/
theorem fourth_prefix_noXi_P12 :
    ∀ l ∈ ([.qel (qmElt (361064, true)), .sign 1 0] : List IdentLetter), l ≠ IdentLetter.xi := by
  intro l hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl <;> exact fun h => IdentLetter.noConfusion h

/-- The target word is the frame-fixing prefix times the translated Fourth source word. -/
theorem fourthP12G_eq :
    fourthP12G = [.qel (qmElt (361064, true)), .sign 1 0] ++ fourthSourceWord (fourthPartnerWord 1) := rfl

set_option maxRecDepth 100000 in
/-- The partner record of `F12+` in the form used by the Fourth assembly. -/
theorem fourthP12_partner :
    ∃ n : List IdentLetter, (∀ l ∈ n, l ≠ IdentLetter.xi) ∧
      FourthPartner n (fourthPartnerWord 1) (generatedAxisGlobalTwelveRepresentative 4) := by
  refine ⟨[.qel (qmElt (361064, true)), .sign 1 0], fourth_prefix_noXi_P12,
    identWordLocal fourthP12H, Or.inl ?_⟩
  rw [← fourthP12G_eq]
  exact fourthP12_ident

set_option maxRecDepth 100000 in
/-- The partner record of `F12+` in the form used by worker `gfifth`. -/
theorem fourthP12_fifth : ∃ g : H, sExtra (rhoLocal (identWordLocal
    (generatedAxisGlobalTwelveFifthBindCosetLetters 3))
      (generatedAxisGlobalTwelveRepresentative 4)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative 3) :=
  ⟨_, fourthP12_ident⟩

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
