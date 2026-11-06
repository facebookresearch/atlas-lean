/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFifthBindIdent0Checks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOctGM

/-! # The Fifth identification (I0-) at the root 0 representative

The exact pairing `pairTriGMO` of the source representation
`generatedAxisGlobalTwelveFifthBind0L` of `h₀ v₅` and the target representation
`generatedAxisGlobalTwelveFifthBind0mW` of `g v₅` is evaluated in separate kernel evaluations
(matrix part, short part with packed octads, odd-short-to-tensor part, packed tensor
dot); their sum is `128`, so `sExtra.symm (h₀ v₅) = g v₅` (`ident_inverse_GMO`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

local notation "H₀" => generatedAxisGlobalTwelveFifthBind0H
local notation "L₀" => generatedAxisGlobalTwelveFifthBind0L
local notation "LX₀" => generatedAxisGlobalTwelveFifthBind0LX
local notation "G₀" => generatedAxisGlobalTwelveFifthBind0mG
local notation "W₀" => generatedAxisGlobalTwelveFifthBind0mW
local notation "WX₀" => generatedAxisGlobalTwelveFifthBind0mWX

/-- The denominators of the two packed tensors. -/
theorem generatedAxisGlobalTwelveFifthBind0m_dens :
    tensorWordDenAll H₀ = 256 ∧
      tensorWordDenAll G₀ = 512 := by
  decide

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing. -/
theorem generatedAxisGlobalTwelveFifthBind0m_pmat :
    triMatF false L₀ W₀ = 3 := by
  decide +kernel

/-- The short scales of the two representations. -/
theorem generatedAxisGlobalTwelveFifthBind0m_sdens :
    (L₀).sden = 1 / 16 ∧ (W₀).sden = 1 / 16 := ⟨rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- The octad terms of the source representation fit the packed octad transform. -/
theorem generatedAxisGlobalTwelveFifthBind0m_octok : octPackOk 32 L₀ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair terms of the short part of the pairing. -/
theorem generatedAxisGlobalTwelveFifthBind0m_pspairs :
    ((W₀).sh.pairs.map (fun q =>
      (q.2 : ℚ) * triPairF false L₀ q.1)).sum = 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad terms of the short part of the pairing (packed octad Fourier, integer form). -/
theorem generatedAxisGlobalTwelveFifthBind0m_psoct :
    ((W₀).sh.oct.map (fun b => (b.2.map (fun q =>
      q.2 * octZ 32 false (octPackX 32 false L₀)
        b.1 q.1)).sum)).sum = 65152 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of the short part of the pairing. -/
theorem generatedAxisGlobalTwelveFifthBind0m_psodd :
    ((W₀).sh.odd.map (fun q =>
      (q.2 : ℚ) * triOddF false L₀ q.1)).sum = 448 := by
  decide +kernel

/-- The short part of the pairing (packed octad Fourier). -/
theorem generatedAxisGlobalTwelveFifthBind0m_pshort :
    triShortO 32 false L₀ W₀ = 61 := by
  rw [triShortO]
  simp only [generatedAxisGlobalTwelveFifthBind0m_octok, ↓reduceIte]
  rw [generatedAxisGlobalTwelveFifthBind0m_pspairs, generatedAxisGlobalTwelveFifthBind0m_psoct,
    generatedAxisGlobalTwelveFifthBind0m_psodd, generatedAxisGlobalTwelveFifthBind0m_sdens.1,
    generatedAxisGlobalTwelveFifthBind0m_sdens.2]
  norm_num

set_option maxRecDepth 100000 in
/-- The odd-short-to-tensor part of the pairing. -/
theorem generatedAxisGlobalTwelveFifthBind0m_podd :
    ((L₀).sh.odd.map (fun q =>
      (L₀).sden * (q.2 : ℚ) * triTCF false W₀ q.1)).sum =
      56 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The packed tensor dot product of the pairing. -/
theorem generatedAxisGlobalTwelveFifthBind0m_ptdot :
    tdotM 64 (trialityTensorT 64 true LX₀) WX₀ =
      18874368 := by
  decide +kernel

/-- The exact pairing of the two representations is `128`. -/
theorem generatedAxisGlobalTwelveFifthBind0m_pair :
    pairTriGMO 32 64 false L₀ generatedAxisGlobalTwelveFifthBind0mW
      LX₀ WX₀
      ((tensorWordDenAll H₀ : ℚ) * 1)
      ((tensorWordDenAll G₀ : ℚ) * 1) = 128 := by
  unfold pairTriGMO
  rw [generatedAxisGlobalTwelveFifthBind0m_pmat, generatedAxisGlobalTwelveFifthBind0m_pshort,
    generatedAxisGlobalTwelveFifthBind0m_podd, show (!false) = true from rfl,
    generatedAxisGlobalTwelveFifthBind0m_ptdot, generatedAxisGlobalTwelveFifthBind0m_dens.1,
    generatedAxisGlobalTwelveFifthBind0m_dens.2]
  norm_num

/-- The identification (I0-). -/
theorem generatedAxisGlobalTwelveFifthBind0m_ident : sExtra.symm (rhoLocal (identWordLocal H₀)
    (generatedAxisGlobalTwelveRepresentative 4)) =
      rhoLocal (identWordLocal G₀) (generatedAxisGlobalTwelveRepresentative 4) := by
  have hX := (tensorWordAll_actual generatedAxisGlobalTwelveFifthBind0H
    (fifthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [generatedAxisGlobalTwelveFifthBind0H_growth]; norm_num) 1).1
  have hY := (tensorWordAll_actual G₀ (fifthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [generatedAxisGlobalTwelveFifthBind0mG_growth]; norm_num) 1).1
  rw [generatedAxisGlobalTwelveFifthBind0H_growth] at hX
  rw [generatedAxisGlobalTwelveFifthBind0mG_growth] at hY
  exact ident_inverse_GMO 4 4 _ _ L₀ generatedAxisGlobalTwelveFifthBind0mW
    (ofList_ok generatedAxisGlobalTwelveFifthBind0pTh
      generatedAxisGlobalTwelveFifthBind0mT_labels.1)
    (ofList_ok generatedAxisGlobalTwelveFifthBind0mTg
      generatedAxisGlobalTwelveFifthBind0mT_labels.2)
    rfl rfl hX hY
    (by norm_num) (by norm_num) generatedAxisGlobalTwelveFifthBind0L_actual
    generatedAxisGlobalTwelveFifthBind0mW_actual generatedAxisGlobalTwelveFifthBind0m_pair

/-- The inverse triality image at the one-xi representative of the Fifth root 0 lies in the
twelve local orbits. -/
theorem generatedAxisGlobalTwelveFifthBind_coset0_neg :
    sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFifthBindCoset 0) generatedFifthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have hc : generatedAxisGlobalTwelveFifthBindCoset 0 =
      identWordLocal generatedAxisGlobalTwelveFifthBind0H := by
    rw [generatedAxisGlobalTwelveFifthBindCoset_eq_word, generatedAxisGlobalTwelveFifthBind0H_eq]
  rw [hc, ← generatedAxisGlobalTwelveFifthBind_rep_four]
  exact generatedAxisGlobalTwelve_mem_of_transport 4 _ generatedAxisGlobalTwelveFifthBind0m_ident

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
