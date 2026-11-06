/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR6pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR6pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR6pPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR6pPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR6pPE
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR6pPM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR6pPP

/-! # The Fourth identification `R6p` (Seventh target)

The exact pairing `pairTriGMO` of the two representations of
`GeneratedAxisGlobalTwelveFourthIdentR6pChecks` is the sum of the parts evaluated in
`...R6pPA` (denominators, octad packing), `...R6pPM` (matrix part), `...R6pPP`,
`...R6pPD`, `...R6pPE` (pair, octad and odd short parts), `...R6pPB` (odd-short-to-tensor part)
and `...R6pPC` (tensor part); it is `128`, so the triality image of the Fourth image is the
Seventh image (`ident_forward_GMO`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The short part of the pairing (packed octad Fourier). -/
theorem fourthR6p_pshort : triShortO 32 true fourthR6pL fourthR6pW = 8223 / 128 := by
  rw [triShortO]
  simp only [fourthR6p_octok, ↓reduceIte]
  rw [fourthR6p_pspairs, fourthR6p_psoct, fourthR6p_psodd]
  rw [fourthR6p_sdens.1, fourthR6p_sdens.2]
  norm_num

/-- The exact pairing of the two representations is `128`. -/
theorem fourthR6p_pair : pairTriGMO 32 104 true fourthR6pL fourthR6pW fourthR6pHX fourthR6pGX
    ((tensorWordDenAll fourthR6pH : ℚ) * 1) ((tensorWordDenAll fourthR6pG : ℚ) * fourthR6pSD) =
      128 := by
  unfold pairTriGMO
  rw [fourthR6p_pmat, fourthR6p_pshort, fourthR6p_podd, show (!true) = false from rfl]
  rw [fourthR6p_ptdot, fourthR6p_dens.1, fourthR6p_dens.2]
  norm_num

/-- The Fourth identification `R6p`. -/
theorem fourthR6p_ident : sExtra (rhoLocal (identWordLocal fourthR6pH)
    (generatedAxisGlobalTwelveRepresentative 3)) =
      rhoLocal (identWordLocal fourthR6pG) (generatedAxisGlobalTwelveRepresentative 6) :=
  ident_forward_GMO 3 6 _ _ fourthR6pL fourthR6pW
    (ofList_ok fourthR6pHT fourthR6pT_labels.1) (ofList_ok fourthR6pGT fourthR6pT_labels.2)
    rfl rfl fourthR6pHX_bnd fourthR6pGX_bnd (by norm_num) (by norm_num) fourthR6pL_actual fourthR6pW_actual fourthR6p_pair

/-- The forward identification at the translated root word of root 6. -/
theorem fourthR6p_forward : FourthIdentForward (generatedAxisGlobalTwelveFourthRootWords 6) :=
  ⟨6, _, fourthR6p_ident⟩

/-- Root 6 of the Fourth forest: both triality images lie in the twelve local orbits. -/
theorem fourth_root6_bound :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 6) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 6) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  fourth_merged_forward 5 fourthR6p_forward

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
