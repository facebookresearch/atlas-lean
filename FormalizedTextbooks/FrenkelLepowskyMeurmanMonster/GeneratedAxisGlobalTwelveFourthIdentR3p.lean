/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR3pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR3pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR3pPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR3pPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR3pPE
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR3pPM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR3pPP

/-! # The Fourth identification `R3p` (Twelfth target)

The exact pairing `pairTriGMO` of the two representations of
`GeneratedAxisGlobalTwelveFourthIdentR3pChecks` is the sum of the parts evaluated in
`...R3pPA` (denominators, octad packing), `...R3pPM` (matrix part), `...R3pPP`,
`...R3pPD`, `...R3pPE` (pair, octad and odd short parts), `...R3pPB` (odd-short-to-tensor part)
and `...R3pPC` (tensor part); it is `128`, so the triality image of the Fourth image is the
Twelfth image (`ident_forward_GMO`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The short part of the pairing (packed octad Fourier). -/
theorem fourthR3p_pshort : triShortO 32 true fourthR3pL fourthR3pW = 2005 / 32 := by
  rw [triShortO]
  simp only [fourthR3p_octok, ↓reduceIte]
  rw [fourthR3p_pspairs, fourthR3p_psoct, fourthR3p_psodd]
  rw [fourthR3p_sdens.1, fourthR3p_sdens.2]
  norm_num

/-- The exact pairing of the two representations is `128`. -/
theorem fourthR3p_pair : pairTriGMO 32 64 true fourthR3pL fourthR3pW fourthR3pHX fourthR3pGX
    ((tensorWordDenAll fourthR3pH : ℚ) * 1) ((tensorWordDenAll fourthR3pG : ℚ) * fourthR3pSD) =
      128 := by
  unfold pairTriGMO
  rw [fourthR3p_pmat, fourthR3p_pshort, fourthR3p_podd, show (!true) = false from rfl]
  rw [fourthR3p_ptdot, fourthR3p_dens.1, fourthR3p_dens.2]
  norm_num

/-- The Fourth identification `R3p`. -/
theorem fourthR3p_ident : sExtra (rhoLocal (identWordLocal fourthR3pH)
    (generatedAxisGlobalTwelveRepresentative 3)) =
      rhoLocal (identWordLocal fourthR3pG) (generatedAxisGlobalTwelveRepresentative 10) :=
  ident_forward_GMO 3 10 _ _ fourthR3pL fourthR3pW
    (ofList_ok fourthR3pHT fourthR3pT_labels.1) (ofList_ok fourthR3pGT fourthR3pT_labels.2)
    rfl rfl fourthR3pHX_bnd fourthR3pGX_bnd (by norm_num) (by norm_num) fourthR3pL_actual fourthR3pW_actual fourthR3p_pair

/-- The forward identification at the translated root word of root 3. -/
theorem fourthR3p_forward : FourthIdentForward (generatedAxisGlobalTwelveFourthRootWords 3) :=
  ⟨10, _, fourthR3p_ident⟩

/-- Root 3 of the Fourth forest: both triality images lie in the twelve local orbits. -/
theorem fourth_root3_bound :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 3) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 3) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  fourth_merged_forward 2 fourthR3p_forward

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
