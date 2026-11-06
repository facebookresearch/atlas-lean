/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentF13Checks

/-! # The Fourth identification (F13-)

The exact pairing `pairTriGMO` of the two representations of
`GeneratedAxisGlobalTwelveFourthIdentF13Checks` is evaluated in four kernel evaluations (matrix
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
theorem fourthF13_dens :
    tensorWordDenAll fourthF13H = 256 ∧ tensorWordDenAll fourthF13G = 512 := by
  decide

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing. -/
theorem fourthF13_pmat : triMatF false fourthF13L fourthF13W = 29 / 8 := by
  decide +kernel

/-- The short scales of the two representations. -/
theorem fourthF13_sdens : fourthF13L.sden = 1 / 8 ∧ fourthF13W.sden = 1 / 8 := ⟨rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- The octad terms of the source representation fit the packed octad transform. -/
theorem fourthF13_octok : octPackOk 32 fourthF13L = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair terms of the short part of the pairing. -/
theorem fourthF13_pspairs :
    (fourthF13W.sh.pairs.map (fun q => (q.2 : ℚ) * triPairF false fourthF13L q.1)).sum =
      21 / 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad terms of the short part of the pairing (packed octad Fourier, integer form). -/
theorem fourthF13_psoct :
    (fourthF13W.sh.oct.map (fun b => (b.2.map (fun q =>
      q.2 * octZ 32 false (octPackX 32 false fourthF13L) b.1 q.1)).sum)).sum = 20000 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of the short part of the pairing. -/
theorem fourthF13_psodd :
    (fourthF13W.sh.odd.map (fun q => (q.2 : ℚ) * triOddF false fourthF13L q.1)).sum =
      224 := by
  decide +kernel

/-- The short part of the pairing (packed octad Fourier). -/
theorem fourthF13_pshort : triShortO 32 false fourthF13L fourthF13W = 547 / 8 := by
  rw [triShortO]
  simp only [fourthF13_octok, ↓reduceIte]
  rw [fourthF13_pspairs, fourthF13_psoct, fourthF13_psodd, fourthF13_sdens.1, fourthF13_sdens.2]
  norm_num

set_option maxRecDepth 100000 in
/-- The odd-short-to-tensor part of the pairing. -/
theorem fourthF13_podd :
    (fourthF13L.sh.odd.map (fun q =>
      fourthF13L.sden * (q.2 : ℚ) * triTCF false fourthF13W q.1)).sum = 56 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The packed tensor dot product of the pairing. -/
theorem fourthF13_ptdot :
    tdotM 64 (trialityTensorT 64 true fourthF13HX) fourthF13GX = 14680064 := by
  decide +kernel

/-- The exact pairing of the two representations is `128`. -/
theorem fourthF13_pair : pairTriGMO 32 64 false fourthF13L fourthF13W fourthF13HX fourthF13GX
    ((tensorWordDenAll fourthF13H : ℚ) * 1) ((tensorWordDenAll fourthF13G : ℚ) * 1) = 128 := by
  unfold pairTriGMO
  rw [fourthF13_pmat, fourthF13_pshort, fourthF13_podd, show (!false) = true from rfl]
  rw [fourthF13_ptdot, fourthF13_dens.1, fourthF13_dens.2]
  norm_num

/-- The identification (F13-). -/
theorem fourthF13_ident : sExtra.symm (rhoLocal (identWordLocal fourthF13H)
    (generatedAxisGlobalTwelveRepresentative 3)) =
      rhoLocal (identWordLocal fourthF13G) (generatedAxisGlobalTwelveRepresentative 3) := by
  have hX := (tensorWordAll_actual fourthF13H (fourthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [fourthF13H_growth]; norm_num) 1).1
  have hY := (tensorWordAll_actual fourthF13G (fourthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [fourthF13G_growth]; norm_num) 1).1
  rw [fourthF13H_growth] at hX
  rw [fourthF13G_growth] at hY
  exact ident_inverse_GMO 3 3 _ _ fourthF13L fourthF13W
    (ofList_ok fourthF13HT fourthF13T_labels.1) (ofList_ok fourthF13GT fourthF13T_labels.2) rfl rfl
    hX hY (by norm_num) (by norm_num) fourthF13L_actual fourthF13W_actual fourthF13_pair

/-- The Fourth inverse identification at the translated representative of root thirteen. -/
theorem fourthF13_inverse : FourthIdentInverse (generatedAxisGlobalTwelveFourthSelfWord 1) :=
  ⟨3, _, fourthF13_ident⟩

/-- Root thirteen of the Fourth forest: both triality images lie in the twelve local orbits. -/
theorem fourth_root13_bound :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 13) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 13) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  fourth_root13_of_ident fourthF13_inverse
end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
