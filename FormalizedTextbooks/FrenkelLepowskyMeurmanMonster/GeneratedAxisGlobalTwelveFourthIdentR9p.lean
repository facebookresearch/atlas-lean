/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR9pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR9pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR9pPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR9pPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR9pPE
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR9pPM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR9pPP

/-! # The Fourth identification `R9p` (Eighth target)

The exact pairing `pairTriGMO` of the two representations of
`GeneratedAxisGlobalTwelveFourthIdentR9pChecks` is the sum of the parts evaluated in
`...R9pPA` (denominators, octad packing), `...R9pPM` (matrix part), `...R9pPP`,
`...R9pPD`, `...R9pPE` (pair, octad and odd short parts), `...R9pPB` (odd-short-to-tensor part)
and `...R9pPC` (tensor part); it is `128`, so the triality image of the Fourth image is the
Eighth image (`ident_forward_GMO`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The short part of the pairing (packed octad Fourier). -/
theorem fourthR9p_pshort : triShortO 32 true fourthR9pL fourthR9pW = 1009 / 16 := by
  rw [triShortO]
  simp only [fourthR9p_octok, ↓reduceIte]
  rw [fourthR9p_pspairs, fourthR9p_psoct, fourthR9p_psodd]
  rw [fourthR9p_sdens.1, fourthR9p_sdens.2]
  norm_num

/-- The exact pairing of the two representations is `128`. -/
theorem fourthR9p_pair : pairTriGMO 32 88 true fourthR9pL fourthR9pW fourthR9pHX fourthR9pGX
    ((tensorWordDenAll fourthR9pH : ℚ) * 1) ((tensorWordDenAll fourthR9pG : ℚ) * fourthR9pSD) =
      128 := by
  unfold pairTriGMO
  rw [fourthR9p_pmat, fourthR9p_pshort, fourthR9p_podd, show (!true) = false from rfl]
  rw [fourthR9p_ptdot, fourthR9p_dens.1, fourthR9p_dens.2]
  norm_num

/-- The Fourth identification `R9p`. -/
theorem fourthR9p_ident : sExtra (rhoLocal (identWordLocal fourthR9pH)
    (generatedAxisGlobalTwelveRepresentative 3)) =
      rhoLocal (identWordLocal fourthR9pG) (generatedAxisGlobalTwelveRepresentative 7) :=
  ident_forward_GMO 3 7 _ _ fourthR9pL fourthR9pW
    (ofList_ok fourthR9pHT fourthR9pT_labels.1) (ofList_ok fourthR9pGT fourthR9pT_labels.2)
    rfl rfl fourthR9pHX_bnd fourthR9pGX_bnd (by norm_num) (by norm_num) fourthR9pL_actual fourthR9pW_actual fourthR9p_pair

/-- The forward identification at the translated root word of root 9. -/
theorem fourthR9p_forward : FourthIdentForward (generatedAxisGlobalTwelveFourthRootWords 9) :=
  ⟨7, _, fourthR9p_ident⟩

/-- Root 9 of the Fourth forest: both triality images lie in the twelve local orbits. -/
theorem fourth_root9_bound :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 9) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 9) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  fourth_merged_forward 8 fourthR9p_forward

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
