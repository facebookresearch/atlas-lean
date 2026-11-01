/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentF12Checks

/-! # The Fourth identification (F12-)

The exact pairing `pairTriGMO` of the two representations of
`GeneratedAxisGlobalTwelveFourthIdentF12Checks` is evaluated in four kernel evaluations (matrix
part, short part with packed octads, odd-short-to-tensor part, packed tensor dot); their sum is
`128`, so the triality image of the source image of the Fourth axis is the target image
(`ident_inverse_GMO`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The denominators of the two packed tensors. -/
theorem fourthF12_dens :
    tensorWordDenAll fourthF12H = 32 ∧ tensorWordDenAll fourthF12G = 512 := by
  decide

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing. -/
theorem fourthF12_pmat : triMatF false fourthF12L fourthF12W = 29 / 8 := by
  decide +kernel

/-- The short scales of the two representations. -/
theorem fourthF12_sdens : fourthF12L.sden = 1 / 8 ∧ fourthF12W.sden = 1 / 8 := ⟨rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- The octad terms of the source representation fit the packed octad transform. -/
theorem fourthF12_octok : octPackOk 32 fourthF12L = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair terms of the short part of the pairing. -/
theorem fourthF12_pspairs :
    (fourthF12W.sh.pairs.map (fun q => (q.2 : ℚ) * triPairF false fourthF12L q.1)).sum =
      37 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad terms of the short part of the pairing (packed octad Fourier, integer form). -/
theorem fourthF12_psoct :
    (fourthF12W.sh.oct.map (fun b => (b.2.map (fun q =>
      q.2 * octZ 32 false (octPackX 32 false fourthF12L) b.1 q.1)).sum)).sum = 16256 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of the short part of the pairing. -/
theorem fourthF12_psodd :
    (fourthF12W.sh.odd.map (fun q => (q.2 : ℚ) * triOddF false fourthF12L q.1)).sum =
      256 := by
  decide +kernel

/-- The short part of the pairing (packed octad Fourier). -/
theorem fourthF12_pshort : triShortO 32 false fourthF12L fourthF12W = 547 / 8 := by
  rw [triShortO]
  simp only [fourthF12_octok, ↓reduceIte]
  rw [fourthF12_pspairs, fourthF12_psoct, fourthF12_psodd, fourthF12_sdens.1, fourthF12_sdens.2]
  norm_num

set_option maxRecDepth 100000 in
/-- The odd-short-to-tensor part of the pairing. -/
theorem fourthF12_podd :
    (fourthF12L.sh.odd.map (fun q =>
      fourthF12L.sden * (q.2 : ℚ) * triTCF false fourthF12W q.1)).sum = 64 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The packed tensor dot product of the pairing. -/
theorem fourthF12_ptdot :
    tdotM 64 (trialityTensorT 64 true fourthF12HX) fourthF12GX = 1572864 := by
  decide +kernel

/-- The exact pairing of the two representations is `128`. -/
theorem fourthF12_pair : pairTriGMO 32 64 false fourthF12L fourthF12W fourthF12HX fourthF12GX
    ((tensorWordDenAll fourthF12H : ℚ) * 1) ((tensorWordDenAll fourthF12G : ℚ) * 1) = 128 := by
  unfold pairTriGMO
  rw [fourthF12_pmat, fourthF12_pshort, fourthF12_podd, show (!false) = true from rfl]
  rw [fourthF12_ptdot, fourthF12_dens.1, fourthF12_dens.2]
  norm_num

/-- The identification (F12-). -/
theorem fourthF12_ident : sExtra.symm (rhoLocal (identWordLocal fourthF12H)
    (generatedAxisGlobalTwelveRepresentative 3)) =
      rhoLocal (identWordLocal fourthF12G) (generatedAxisGlobalTwelveRepresentative 3) := by
  have hX := (tensorWordAll_actual fourthF12H (fourthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [fourthF12H_growth]; norm_num) 1).1
  have hY := (tensorWordAll_actual fourthF12G (fourthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [fourthF12G_growth]; norm_num) 1).1
  rw [fourthF12H_growth] at hX
  rw [fourthF12G_growth] at hY
  exact ident_inverse_GMO 3 3 _ _ fourthF12L fourthF12W
    (ofList_ok fourthF12HT fourthF12T_labels.1) (ofList_ok fourthF12GT fourthF12T_labels.2) rfl rfl
    hX hY (by norm_num) (by norm_num) fourthF12L_actual fourthF12W_actual fourthF12_pair

/-- The Fourth-class inverse identification at the translated pair representative of root twelve. -/
theorem fourthF12_self : FourthSelfInverse (generatedAxisGlobalTwelveFourthPairWord 1) :=
  ⟨_, fourthF12_ident⟩
end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
