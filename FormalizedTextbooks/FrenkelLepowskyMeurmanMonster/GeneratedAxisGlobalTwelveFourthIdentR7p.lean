/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR7pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR7pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR7pPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR7pPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR7pPE
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR7pPM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR7pPP

/-! # The Fourth identification `R7p` (Seventh target)

The exact pairing `pairTriGMO` of the two representations of
`GeneratedAxisGlobalTwelveFourthIdentR7pChecks` is the sum of the parts evaluated in
`...R7pPA` (denominators, octad packing), `...R7pPM` (matrix part), `...R7pPP`,
`...R7pPD`, `...R7pPE` (pair, octad and odd short parts), `...R7pPB` (odd-short-to-tensor part)
and `...R7pPC` (tensor part); it is `128`, so the triality image of the Fourth image is the
Seventh image (`ident_forward_GMO`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The short part of the pairing (packed octad Fourier). -/
theorem fourthR7p_pshort : triShortO 32 true fourthR7pL fourthR7pW = 8223 / 128 := by
  rw [triShortO]
  simp only [fourthR7p_octok, ↓reduceIte]
  rw [fourthR7p_pspairs, fourthR7p_psoct, fourthR7p_psodd]
  rw [fourthR7p_sdens.1, fourthR7p_sdens.2]
  norm_num

/-- The exact pairing of the two representations is `128`. -/
theorem fourthR7p_pair : pairTriGMO 32 104 true fourthR7pL fourthR7pW fourthR7pHX fourthR7pGX
    ((tensorWordDenAll fourthR7pH : ℚ) * 1) ((tensorWordDenAll fourthR7pG : ℚ) * fourthR7pSD) =
      128 := by
  unfold pairTriGMO
  rw [fourthR7p_pmat, fourthR7p_pshort, fourthR7p_podd, show (!true) = false from rfl]
  rw [fourthR7p_ptdot, fourthR7p_dens.1, fourthR7p_dens.2]
  norm_num

/-- The Fourth identification `R7p`. -/
theorem fourthR7p_ident : sExtra (rhoLocal (identWordLocal fourthR7pH)
    (generatedAxisGlobalTwelveRepresentative 3)) =
      rhoLocal (identWordLocal fourthR7pG) (generatedAxisGlobalTwelveRepresentative 6) :=
  ident_forward_GMO 3 6 _ _ fourthR7pL fourthR7pW
    (ofList_ok fourthR7pHT fourthR7pT_labels.1) (ofList_ok fourthR7pGT fourthR7pT_labels.2)
    rfl rfl fourthR7pHX_bnd fourthR7pGX_bnd (by norm_num) (by norm_num) fourthR7pL_actual fourthR7pW_actual fourthR7p_pair

/-- The forward identification at the translated root word of root 7. -/
theorem fourthR7p_forward : FourthIdentForward (generatedAxisGlobalTwelveFourthRootWords 7) :=
  ⟨6, _, fourthR7p_ident⟩

/-- Root 7 of the Fourth forest: both triality images lie in the twelve local orbits. -/
theorem fourth_root7_bound :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 7) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 7) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  fourth_merged_forward 6 fourthR7p_forward

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
