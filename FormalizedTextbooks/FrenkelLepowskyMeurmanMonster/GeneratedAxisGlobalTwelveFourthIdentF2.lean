/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentF2Checks

/-! # The Fourth identification (F2-)

The exact pairing `pairTriGMO` of the two representations of
`GeneratedAxisGlobalTwelveFourthIdentF2Checks` is evaluated in four kernel evaluations (matrix
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
theorem fourthF2_dens :
    tensorWordDenAll fourthF2H = 256 ∧ tensorWordDenAll fourthF2G = 512 := by
  decide

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing. -/
theorem fourthF2_pmat : triMatF false fourthF2L fourthF2W = 29 / 8 := by
  decide +kernel

/-- The short scales of the two representations. -/
theorem fourthF2_sdens : fourthF2L.sden = 1 / 8 ∧ fourthF2W.sden = 1 / 8 := ⟨rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- The octad terms of the source representation fit the packed octad transform. -/
theorem fourthF2_octok : octPackOk 32 fourthF2L = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair terms of the short part of the pairing. -/
theorem fourthF2_pspairs :
    (fourthF2W.sh.pairs.map (fun q => (q.2 : ℚ) * triPairF false fourthF2L q.1)).sum =
      25 / 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad terms of the short part of the pairing (packed octad Fourier, integer form). -/
theorem fourthF2_psoct :
    (fourthF2W.sh.oct.map (fun b => (b.2.map (fun q =>
      q.2 * octZ 32 false (octPackX 32 false fourthF2L) b.1 q.1)).sum)).sum = 19872 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of the short part of the pairing. -/
theorem fourthF2_psodd :
    (fourthF2W.sh.odd.map (fun q => (q.2 : ℚ) * triOddF false fourthF2L q.1)).sum =
      224 := by
  decide +kernel

/-- The short part of the pairing (packed octad Fourier). -/
theorem fourthF2_pshort : triShortO 32 false fourthF2L fourthF2W = 547 / 8 := by
  rw [triShortO]
  simp only [fourthF2_octok, ↓reduceIte]
  rw [fourthF2_pspairs, fourthF2_psoct, fourthF2_psodd, fourthF2_sdens.1, fourthF2_sdens.2]
  norm_num

set_option maxRecDepth 100000 in
/-- The odd-short-to-tensor part of the pairing. -/
theorem fourthF2_podd :
    (fourthF2L.sh.odd.map (fun q => fourthF2L.sden * (q.2 : ℚ) * triTCF false fourthF2W q.1)).sum =
      56 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The packed tensor dot product of the pairing. -/
theorem fourthF2_ptdot : tdotM 64 (trialityTensorT 64 true fourthF2HX) fourthF2GX = 14680064 := by
  decide +kernel

/-- The exact pairing of the two representations is `128`. -/
theorem fourthF2_pair : pairTriGMO 32 64 false fourthF2L fourthF2W fourthF2HX fourthF2GX
    ((tensorWordDenAll fourthF2H : ℚ) * 1) ((tensorWordDenAll fourthF2G : ℚ) * 1) = 128 := by
  unfold pairTriGMO
  rw [fourthF2_pmat, fourthF2_pshort, fourthF2_podd, show (!false) = true from rfl, fourthF2_ptdot,
    fourthF2_dens.1, fourthF2_dens.2]
  norm_num

/-- The identification (F2-). -/
theorem fourthF2_ident : sExtra.symm (rhoLocal (identWordLocal fourthF2H)
    (generatedAxisGlobalTwelveRepresentative 3)) =
      rhoLocal (identWordLocal fourthF2G) (generatedAxisGlobalTwelveRepresentative 3) := by
  have hX := (tensorWordAll_actual fourthF2H (fourthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [fourthF2H_growth]; norm_num) 1).1
  have hY := (tensorWordAll_actual fourthF2G (fourthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [fourthF2G_growth]; norm_num) 1).1
  rw [fourthF2H_growth] at hX
  rw [fourthF2G_growth] at hY
  exact ident_inverse_GMO 3 3 _ _ fourthF2L fourthF2W
    (ofList_ok fourthF2HT fourthF2T_labels.1) (ofList_ok fourthF2GT fourthF2T_labels.2) rfl rfl
    hX hY (by norm_num) (by norm_num) fourthF2L_actual fourthF2W_actual fourthF2_pair

/-- The Fourth inverse identification at the translated representative of root two. -/
theorem fourthF2_inverse : FourthIdentInverse (generatedAxisGlobalTwelveFourthSelfWord 0) :=
  ⟨3, _, fourthF2_ident⟩

/-- Root two of the Fourth forest: both triality images lie in the twelve local orbits. -/
theorem fourth_root2_bound :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 2) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 2) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  fourth_root2_of_ident fourthF2_inverse
end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
