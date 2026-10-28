/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR14pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR14pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR14pPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR14pPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR14pPE
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR14pPM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR14pPP

/-! # The Fourth identification `R14p` (Seventh target)

The exact pairing `pairTriGMO` of the two representations of
`GeneratedAxisGlobalTwelveFourthIdentR14pChecks` is the sum of the parts evaluated in
`...R14pPA` (denominators, octad packing), `...R14pPM` (matrix part), `...R14pPP`,
`...R14pPD`, `...R14pPE` (pair, octad and odd short parts), `...R14pPB` (odd-short-to-tensor part)
and `...R14pPC` (tensor part); it is `128`, so the triality image of the Fourth image is the
Seventh image (`ident_forward_GMO`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The short part of the pairing (packed octad Fourier). -/
theorem fourthR14p_pshort : triShortO 32 true fourthR14pL fourthR14pW = 8223 / 128 := by
  rw [triShortO]
  simp only [fourthR14p_octok, ↓reduceIte]
  rw [fourthR14p_pspairs, fourthR14p_psoct, fourthR14p_psodd]
  rw [fourthR14p_sdens.1, fourthR14p_sdens.2]
  norm_num

/-- The exact pairing of the two representations is `128`. -/
theorem fourthR14p_pair : pairTriGMO 32 104 true fourthR14pL fourthR14pW fourthR14pHX fourthR14pGX
    ((tensorWordDenAll fourthR14pH : ℚ) * 1) ((tensorWordDenAll fourthR14pG : ℚ) * fourthR14pSD) =
      128 := by
  unfold pairTriGMO
  rw [fourthR14p_pmat, fourthR14p_pshort, fourthR14p_podd, show (!true) = false from rfl]
  rw [fourthR14p_ptdot, fourthR14p_dens.1, fourthR14p_dens.2]
  norm_num

/-- The Fourth identification `R14p`. -/
theorem fourthR14p_ident : sExtra (rhoLocal (identWordLocal fourthR14pH)
    (generatedAxisGlobalTwelveRepresentative 3)) =
      rhoLocal (identWordLocal fourthR14pG) (generatedAxisGlobalTwelveRepresentative 6) :=
  ident_forward_GMO 3 6 _ _ fourthR14pL fourthR14pW
    (ofList_ok fourthR14pHT fourthR14pT_labels.1) (ofList_ok fourthR14pGT fourthR14pT_labels.2)
    rfl rfl fourthR14pHX_bnd fourthR14pGX_bnd (by norm_num) (by norm_num) fourthR14pL_actual fourthR14pW_actual fourthR14p_pair

/-- The forward identification at the translated root word of root 14. -/
theorem fourthR14p_forward : FourthIdentForward (generatedAxisGlobalTwelveFourthRootWords 14) :=
  ⟨6, _, fourthR14p_ident⟩

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
