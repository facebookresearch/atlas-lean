/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentF1Checks

/-! # The Fourth identification (F1+)

The exact pairing `pairTriGMO` of the two representations of
`GeneratedAxisGlobalTwelveFourthIdentF1Checks` is evaluated in four kernel evaluations (matrix
part, short part with packed octads, odd-short-to-tensor part, packed tensor dot); their sum is
`128`, so the triality image of the source image of the Fourth axis is the target image
(`ident_forward_GMO`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The denominators of the two packed tensors. -/
theorem fourthF1_dens :
    tensorWordDenAll fourthF1H = 16 ∧ tensorWordDenAll fourthF1G = 512 := by
  decide

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing. -/
theorem fourthF1_pmat : triMatF true fourthF1L fourthF1W = 29 / 8 := by
  decide +kernel

/-- The short scales of the two representations. -/
theorem fourthF1_sdens : fourthF1L.sden = 1 / 8 ∧ fourthF1W.sden = 1 / 8 := ⟨rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- The octad terms of the source representation fit the packed octad transform. -/
theorem fourthF1_octok : octPackOk 32 fourthF1L = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair terms of the short part of the pairing. -/
theorem fourthF1_pspairs :
    (fourthF1W.sh.pairs.map (fun q => (q.2 : ℚ) * triPairF true fourthF1L q.1)).sum =
      9 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad terms of the short part of the pairing (packed octad Fourier, integer form). -/
theorem fourthF1_psoct :
    (fourthF1W.sh.oct.map (fun b => (b.2.map (fun q =>
      q.2 * octZ 32 true (octPackX 32 true fourthF1L) b.1 q.1)).sum)).sum = 18048 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of the short part of the pairing. -/
theorem fourthF1_psodd :
    (fourthF1W.sh.odd.map (fun q => (q.2 : ℚ) * triOddF true fourthF1L q.1)).sum =
      256 := by
  decide +kernel

/-- The short part of the pairing (packed octad Fourier). -/
theorem fourthF1_pshort : triShortO 32 true fourthF1L fourthF1W = 547 / 8 := by
  rw [triShortO]
  simp only [fourthF1_octok, ↓reduceIte]
  rw [fourthF1_pspairs, fourthF1_psoct, fourthF1_psodd, fourthF1_sdens.1, fourthF1_sdens.2]
  norm_num

set_option maxRecDepth 100000 in
/-- The odd-short-to-tensor part of the pairing. -/
theorem fourthF1_podd :
    (fourthF1L.sh.odd.map (fun q =>
      fourthF1L.sden * (q.2 : ℚ) * triTCF true fourthF1W q.1)).sum = 64 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The packed tensor dot product of the pairing. -/
theorem fourthF1_ptdot :
    tdotM 64 (trialityTensorT 64 false fourthF1HX) fourthF1GX = 786432 := by
  decide +kernel

/-- The exact pairing of the two representations is `128`. -/
theorem fourthF1_pair : pairTriGMO 32 64 true fourthF1L fourthF1W fourthF1HX fourthF1GX
    ((tensorWordDenAll fourthF1H : ℚ) * 1) ((tensorWordDenAll fourthF1G : ℚ) * 1) = 128 := by
  unfold pairTriGMO
  rw [fourthF1_pmat, fourthF1_pshort, fourthF1_podd, show (!true) = false from rfl]
  rw [fourthF1_ptdot, fourthF1_dens.1, fourthF1_dens.2]
  norm_num

/-- The identification (F1+). -/
theorem fourthF1_ident : sExtra (rhoLocal (identWordLocal fourthF1H)
    (generatedAxisGlobalTwelveRepresentative 3)) =
      rhoLocal (identWordLocal fourthF1G) (generatedAxisGlobalTwelveRepresentative 3) := by
  have hX := (tensorWordAll_actual fourthF1H (fourthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [fourthF1H_growth]; norm_num) 1).1
  have hY := (tensorWordAll_actual fourthF1G (fourthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [fourthF1G_growth]; norm_num) 1).1
  rw [fourthF1H_growth] at hX
  rw [fourthF1G_growth] at hY
  exact ident_forward_GMO 3 3 _ _ fourthF1L fourthF1W
    (ofList_ok fourthF1HT fourthF1T_labels.1) (ofList_ok fourthF1GT fourthF1T_labels.2) rfl rfl
    hX hY (by norm_num) (by norm_num) fourthF1L_actual fourthF1W_actual fourthF1_pair

/-- The Fourth-class forward identification at the translated pair representative of root one. -/
theorem fourthF1_self : FourthSelfForward (generatedAxisGlobalTwelveFourthPairWord 0) :=
  ⟨_, fourthF1_ident⟩
end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
