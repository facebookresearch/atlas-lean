/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFifthBindIdent6bChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOctGM

/-! # The Fifth identification (I6-) at the root 6 representative

The exact pairing `pairTriGMO` of the source representation
`generatedAxisGlobalTwelveFifthBind6pL` of `h₆ v₅` and the target representation
`generatedAxisGlobalTwelveFifthBind6bW` of `g v₅` is evaluated in separate kernel evaluations
(matrix part, short part with packed octads, odd-short-to-tensor part, packed tensor
dot); their sum is `128`, so `sExtra.symm (h₆ v₅) = g v₅` (`ident_inverse_GMO`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

local notation "H₆" => generatedAxisGlobalTwelveFifthBind6pH
local notation "L₆" => generatedAxisGlobalTwelveFifthBind6pL
local notation "LX₆" => generatedAxisGlobalTwelveFifthBind6pLX
local notation "G₆" => generatedAxisGlobalTwelveFifthBind6bG
local notation "W₆" => generatedAxisGlobalTwelveFifthBind6bW
local notation "WX₆" => generatedAxisGlobalTwelveFifthBind6bWX

/-- The denominators of the two packed tensors. -/
theorem generatedAxisGlobalTwelveFifthBind6b_dens :
    tensorWordDenAll H₆ = 256 ∧
      tensorWordDenAll G₆ = 512 := by
  decide

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing. -/
theorem generatedAxisGlobalTwelveFifthBind6b_pmat :
    triMatF false L₆ W₆ = 3 := by
  decide +kernel

/-- The short scales of the two representations. -/
theorem generatedAxisGlobalTwelveFifthBind6b_sdens :
    (L₆).sden = 1 / 16 ∧ (W₆).sden = 1 / 16 := ⟨rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- The octad terms of the source representation fit the packed octad transform. -/
theorem generatedAxisGlobalTwelveFifthBind6b_octok : octPackOk 32 L₆ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair terms of the short part of the pairing. -/
theorem generatedAxisGlobalTwelveFifthBind6b_pspairs :
    ((W₆).sh.pairs.map (fun q =>
      (q.2 : ℚ) * triPairF false L₆ q.1)).sum = 8 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad terms of the short part of the pairing (packed octad Fourier, integer form). -/
theorem generatedAxisGlobalTwelveFifthBind6b_psoct :
    ((W₆).sh.oct.map (fun b => (b.2.map (fun q =>
      q.2 * octZ 32 false (octPackX 32 false L₆)
        b.1 q.1)).sum)).sum = 58368 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of the short part of the pairing. -/
theorem generatedAxisGlobalTwelveFifthBind6b_psodd :
    ((W₆).sh.odd.map (fun q =>
      (q.2 : ℚ) * triOddF false L₆ q.1)).sum = 512 := by
  decide +kernel

/-- The short part of the pairing (packed octad Fourier). -/
theorem generatedAxisGlobalTwelveFifthBind6b_pshort :
    triShortO 32 false L₆ W₆ = 61 := by
  rw [triShortO]
  simp only [generatedAxisGlobalTwelveFifthBind6b_octok, ↓reduceIte]
  rw [generatedAxisGlobalTwelveFifthBind6b_pspairs, generatedAxisGlobalTwelveFifthBind6b_psoct,
    generatedAxisGlobalTwelveFifthBind6b_psodd, generatedAxisGlobalTwelveFifthBind6b_sdens.1,
    generatedAxisGlobalTwelveFifthBind6b_sdens.2]
  norm_num

set_option maxRecDepth 100000 in
/-- The odd-short-to-tensor part of the pairing. -/
theorem generatedAxisGlobalTwelveFifthBind6b_podd :
    ((L₆).sh.odd.map (fun q =>
      (L₆).sden * (q.2 : ℚ) * triTCF false W₆ q.1)).sum =
      64 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The packed tensor dot product of the pairing. -/
theorem generatedAxisGlobalTwelveFifthBind6b_ptdot :
    tdotM 64 (trialityTensorT 64 true LX₆) WX₆ =
      16777216 := by
  decide +kernel

/-- The exact pairing of the two representations is `128`. -/
theorem generatedAxisGlobalTwelveFifthBind6b_pair :
    pairTriGMO 32 64 false L₆ generatedAxisGlobalTwelveFifthBind6bW
      LX₆ WX₆
      ((tensorWordDenAll H₆ : ℚ) * 1)
      ((tensorWordDenAll G₆ : ℚ) * 1) = 128 := by
  unfold pairTriGMO
  rw [generatedAxisGlobalTwelveFifthBind6b_pmat, generatedAxisGlobalTwelveFifthBind6b_pshort,
    generatedAxisGlobalTwelveFifthBind6b_podd, show (!false) = true from rfl,
    generatedAxisGlobalTwelveFifthBind6b_ptdot, generatedAxisGlobalTwelveFifthBind6b_dens.1,
    generatedAxisGlobalTwelveFifthBind6b_dens.2]
  norm_num

/-- The identification (I6-). -/
theorem generatedAxisGlobalTwelveFifthBind6b_ident : sExtra.symm (rhoLocal (identWordLocal H₆)
    (generatedAxisGlobalTwelveRepresentative 4)) =
      rhoLocal (identWordLocal G₆) (generatedAxisGlobalTwelveRepresentative 4) := by
  have hX := (tensorWordAll_actual generatedAxisGlobalTwelveFifthBind6pH
    (fifthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [generatedAxisGlobalTwelveFifthBind6pH_growth]; norm_num) 1).1
  have hY := (tensorWordAll_actual G₆ (fifthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [generatedAxisGlobalTwelveFifthBind6bG_growth]; norm_num) 1).1
  rw [generatedAxisGlobalTwelveFifthBind6pH_growth] at hX
  rw [generatedAxisGlobalTwelveFifthBind6bG_growth] at hY
  exact ident_inverse_GMO 4 4 _ _ L₆ generatedAxisGlobalTwelveFifthBind6bW
    (ofList_ok generatedAxisGlobalTwelveFifthBind6pTh
      generatedAxisGlobalTwelveFifthBind6pT_labels.1)
    (ofList_ok generatedAxisGlobalTwelveFifthBind6bTg generatedAxisGlobalTwelveFifthBind6bTg_labels)
    rfl rfl hX hY
    (by norm_num) (by norm_num) generatedAxisGlobalTwelveFifthBind6pL_actual
    generatedAxisGlobalTwelveFifthBind6bW_actual generatedAxisGlobalTwelveFifthBind6b_pair

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
