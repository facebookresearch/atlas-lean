/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentF15Checks

/-! # The Fourth identification (F15-)

The exact pairing `pairTriGMO` of the two representations of
`GeneratedAxisGlobalTwelveFourthIdentF15Checks` is evaluated in four kernel evaluations (matrix
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
theorem fourthF15_dens :
    tensorWordDenAll fourthF15H = 512 ∧ tensorWordDenAll fourthF15G = 512 := by
  decide

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing. -/
theorem fourthF15_pmat : triMatF false fourthF15L fourthF15W = 29 / 8 := by
  decide +kernel

/-- The short scales of the two representations. -/
theorem fourthF15_sdens : fourthF15L.sden = 1 / 8 ∧ fourthF15W.sden = 1 / 8 := ⟨rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- The octad terms of the source representation fit the packed octad transform. -/
theorem fourthF15_octok : octPackOk 32 fourthF15L = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair terms of the short part of the pairing. -/
theorem fourthF15_pspairs :
    (fourthF15W.sh.pairs.map (fun q => (q.2 : ℚ) * triPairF false fourthF15L q.1)).sum =
      31 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad terms of the short part of the pairing (packed octad Fourier, integer form). -/
theorem fourthF15_psoct :
    (fourthF15W.sh.oct.map (fun b => (b.2.map (fun q =>
      q.2 * octZ 32 false (octPackX 32 false fourthF15L) b.1 q.1)).sum)).sum = 16640 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of the short part of the pairing. -/
theorem fourthF15_psodd :
    (fourthF15W.sh.odd.map (fun q => (q.2 : ℚ) * triOddF false fourthF15L q.1)).sum =
      256 := by
  decide +kernel

/-- The short part of the pairing (packed octad Fourier). -/
theorem fourthF15_pshort : triShortO 32 false fourthF15L fourthF15W = 547 / 8 := by
  rw [triShortO]
  simp only [fourthF15_octok, ↓reduceIte]
  rw [fourthF15_pspairs, fourthF15_psoct, fourthF15_psodd, fourthF15_sdens.1, fourthF15_sdens.2]
  norm_num

set_option maxRecDepth 100000 in
/-- The odd-short-to-tensor part of the pairing. -/
theorem fourthF15_podd :
    (fourthF15L.sh.odd.map (fun q =>
      fourthF15L.sden * (q.2 : ℚ) * triTCF false fourthF15W q.1)).sum = 64 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The packed tensor dot product of the pairing. -/
theorem fourthF15_ptdot :
    tdotM 72 (trialityTensorT 72 true fourthF15HX) fourthF15GX = 25165824 := by
  decide +kernel

/-- The exact pairing of the two representations is `128`. -/
theorem fourthF15_pair : pairTriGMO 32 72 false fourthF15L fourthF15W fourthF15HX fourthF15GX
    ((tensorWordDenAll fourthF15H : ℚ) * 1) ((tensorWordDenAll fourthF15G : ℚ) * 1) = 128 := by
  unfold pairTriGMO
  rw [fourthF15_pmat, fourthF15_pshort, fourthF15_podd, show (!false) = true from rfl]
  rw [fourthF15_ptdot, fourthF15_dens.1, fourthF15_dens.2]
  norm_num

/-- The identification (F15-). -/
theorem fourthF15_ident : sExtra.symm (rhoLocal (identWordLocal fourthF15H)
    (generatedAxisGlobalTwelveRepresentative 3)) =
      rhoLocal (identWordLocal fourthF15G) (generatedAxisGlobalTwelveRepresentative 3) := by
  have hX := (tensorWordAll_actual fourthF15H (fourthSrcXW_bnd (w := 72) (by norm_num))
    (by rw [fourthF15H_growth]; norm_num) 1).1
  have hY := (tensorWordAll_actual fourthF15G (fourthSrcXW_bnd (w := 72) (by norm_num))
    (by rw [fourthF15G_growth]; norm_num) 1).1
  rw [fourthF15H_growth] at hX
  rw [fourthF15G_growth] at hY
  exact ident_inverse_GMO 3 3 _ _ fourthF15L fourthF15W
    (ofList_ok fourthF15HT fourthF15T_labels.1) (ofList_ok fourthF15GT fourthF15T_labels.2) rfl rfl
    hX hY (by norm_num) (by norm_num) fourthF15L_actual fourthF15W_actual fourthF15_pair

/-- The Fourth-class inverse identification at the translated representative of root fifteen. -/
theorem fourthF15_self : FourthSelfInverse (generatedAxisGlobalTwelveFourthSelfWord 2) :=
  ⟨_, fourthF15_ident⟩
end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
