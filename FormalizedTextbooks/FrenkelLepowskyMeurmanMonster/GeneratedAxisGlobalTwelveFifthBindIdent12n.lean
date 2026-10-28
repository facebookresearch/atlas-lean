/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFifthBindIdent12Checks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOctGM

/-! # The Fifth to Fourth identification (I12-) at the root 12 representative

The exact pairing `pairTriGMO` of the source representation
`generatedAxisGlobalTwelveFifthBind12L` of `h₁₂ v₅` and the target representation
`generatedAxisGlobalTwelveFifthBind12mW` of `g v₄` is evaluated in separate kernel evaluations
(matrix part, short part with packed octads, odd-short-to-tensor part, packed tensor
dot); their sum is `128`, so `sExtra.symm (h₁₂ v₅) = g v₄` (`ident_inverse_GMO`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

local notation "H₁₂" => generatedAxisGlobalTwelveFifthBind12H
local notation "L₁₂" => generatedAxisGlobalTwelveFifthBind12L
local notation "LX₁₂" => generatedAxisGlobalTwelveFifthBind12LX
local notation "G₁₂" => generatedAxisGlobalTwelveFifthBind12mG
local notation "W₁₂" => generatedAxisGlobalTwelveFifthBind12mW
local notation "WX₁₂" => generatedAxisGlobalTwelveFifthBind12mWX

/-- The denominators of the two packed tensors. -/
theorem generatedAxisGlobalTwelveFifthBind12m_dens :
    tensorWordDenAll H₁₂ = 256 ∧
      tensorWordDenAll G₁₂ = 32 := by
  decide

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing. -/
theorem generatedAxisGlobalTwelveFifthBind12m_pmat :
    triMatF false L₁₂ W₁₂ = 29 / 8 := by
  decide +kernel

/-- The short scales of the two representations. -/
theorem generatedAxisGlobalTwelveFifthBind12m_sdens :
    (L₁₂).sden = 1 / 16 ∧ (W₁₂).sden = 1 / 8 := ⟨rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- The octad terms of the source representation fit the packed octad transform. -/
theorem generatedAxisGlobalTwelveFifthBind12m_octok : octPackOk 32 L₁₂ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair terms of the short part of the pairing. -/
theorem generatedAxisGlobalTwelveFifthBind12m_pspairs :
    ((W₁₂).sh.pairs.map (fun q =>
      (q.2 : ℚ) * triPairF false L₁₂ q.1)).sum = 9 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad terms of the short part of the pairing (packed octad Fourier, integer form). -/
theorem generatedAxisGlobalTwelveFifthBind12m_psoct :
    ((W₁₂).sh.oct.map (fun b => (b.2.map (fun q =>
      q.2 * octZ 32 false (octPackX 32 false L₁₂)
        b.1 q.1)).sum)).sum = 36096 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of the short part of the pairing. -/
theorem generatedAxisGlobalTwelveFifthBind12m_psodd :
    ((W₁₂).sh.odd.map (fun q =>
      (q.2 : ℚ) * triOddF false L₁₂ q.1)).sum = 256 := by
  decide +kernel

/-- The short part of the pairing (packed octad Fourier). -/
theorem generatedAxisGlobalTwelveFifthBind12m_pshort :
    triShortO 32 false L₁₂ W₁₂ = 547 / 8 := by
  rw [triShortO]
  simp only [generatedAxisGlobalTwelveFifthBind12m_octok, ↓reduceIte]
  rw [generatedAxisGlobalTwelveFifthBind12m_pspairs, generatedAxisGlobalTwelveFifthBind12m_psoct,
    generatedAxisGlobalTwelveFifthBind12m_psodd, generatedAxisGlobalTwelveFifthBind12m_sdens.1,
    generatedAxisGlobalTwelveFifthBind12m_sdens.2]
  norm_num

set_option maxRecDepth 100000 in
/-- The odd-short-to-tensor part of the pairing. -/
theorem generatedAxisGlobalTwelveFifthBind12m_podd :
    ((L₁₂).sh.odd.map (fun q =>
      (L₁₂).sden * (q.2 : ℚ) * triTCF false W₁₂ q.1)).sum =
      48 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The packed tensor dot product of the pairing. -/
theorem generatedAxisGlobalTwelveFifthBind12m_ptdot :
    tdotM 64 (trialityTensorT 64 true LX₁₂) WX₁₂ =
      1048576 := by
  decide +kernel

/-- The exact pairing of the two representations is `128`. -/
theorem generatedAxisGlobalTwelveFifthBind12m_pair :
    pairTriGMO 32 64 false L₁₂ generatedAxisGlobalTwelveFifthBind12mW
      LX₁₂ WX₁₂
      ((tensorWordDenAll H₁₂ : ℚ) * 1)
      ((tensorWordDenAll G₁₂ : ℚ) * 1) = 128 := by
  unfold pairTriGMO
  rw [generatedAxisGlobalTwelveFifthBind12m_pmat, generatedAxisGlobalTwelveFifthBind12m_pshort,
    generatedAxisGlobalTwelveFifthBind12m_podd, show (!false) = true from rfl,
    generatedAxisGlobalTwelveFifthBind12m_ptdot, generatedAxisGlobalTwelveFifthBind12m_dens.1,
    generatedAxisGlobalTwelveFifthBind12m_dens.2]
  norm_num

/-- The identification (I12-). -/
theorem generatedAxisGlobalTwelveFifthBind12m_ident : sExtra.symm (rhoLocal (identWordLocal H₁₂)
    (generatedAxisGlobalTwelveRepresentative 4)) =
      rhoLocal (identWordLocal G₁₂) (generatedAxisGlobalTwelveRepresentative 3) := by
  have hX := (tensorWordAll_actual generatedAxisGlobalTwelveFifthBind12H
    (fifthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [generatedAxisGlobalTwelveFifthBind12H_growth]; norm_num) 1).1
  have hY := (tensorWordAll_actual G₁₂ (fourthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [generatedAxisGlobalTwelveFifthBind12mG_growth]; norm_num) 1).1
  rw [generatedAxisGlobalTwelveFifthBind12H_growth] at hX
  rw [generatedAxisGlobalTwelveFifthBind12mG_growth] at hY
  exact ident_inverse_GMO 4 3 _ _ L₁₂ generatedAxisGlobalTwelveFifthBind12mW
    (ofList_ok generatedAxisGlobalTwelveFifthBind12pTh
      generatedAxisGlobalTwelveFifthBind12mT_labels.1)
    (ofList_ok generatedAxisGlobalTwelveFifthBind12mTg
      generatedAxisGlobalTwelveFifthBind12mT_labels.2)
    rfl rfl hX hY
    (by norm_num) (by norm_num) generatedAxisGlobalTwelveFifthBind12L_actual
    generatedAxisGlobalTwelveFifthBind12mW_actual generatedAxisGlobalTwelveFifthBind12m_pair

/-- The inverse triality image at the one-xi representative of the Fifth root 12 lies in the
twelve local orbits. -/
theorem generatedAxisGlobalTwelveFifthBind_coset12_neg :
    sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFifthBindCoset 3) generatedFifthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have hc : generatedAxisGlobalTwelveFifthBindCoset 3 =
      identWordLocal generatedAxisGlobalTwelveFifthBind12H := by
    rw [generatedAxisGlobalTwelveFifthBindCoset_eq_word, generatedAxisGlobalTwelveFifthBind12H_eq]
  rw [hc, ← generatedAxisGlobalTwelveFifthBind_rep_four]
  exact generatedAxisGlobalTwelve_mem_of_transport 3 _ generatedAxisGlobalTwelveFifthBind12m_ident

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
