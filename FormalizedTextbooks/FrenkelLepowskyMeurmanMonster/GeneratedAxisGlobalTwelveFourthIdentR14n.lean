/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR14nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR14nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR14nPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR14nPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR14nPE
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR14nPM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR14nPP

/-! # The Fourth identification `R14n` (Sixth target)

The exact pairing `pairTriGMO` of the two representations of
`GeneratedAxisGlobalTwelveFourthIdentR14nChecks` is the sum of the parts evaluated in
`...R14nPA` (denominators, octad packing), `...R14nPM` (matrix part), `...R14nPP`,
`...R14nPD`, `...R14nPE` (pair, octad and odd short parts), `...R14nPB` (odd-short-to-tensor part)
and `...R14nPC` (tensor part); it is `128`, so the triality image of the Fourth image is the
Sixth image (`ident_inverse_GMO`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The short part of the pairing (packed octad Fourier). -/
theorem fourthR14n_pshort : triShortO 32 false fourthR14nL fourthR14nW = 8111 / 128 := by
  rw [triShortO]
  simp only [fourthR14n_octok, ↓reduceIte]
  rw [fourthR14n_pspairs, fourthR14n_psoct, fourthR14n_psodd]
  rw [fourthR14n_sdens.1, fourthR14n_sdens.2]
  norm_num

/-- The exact pairing of the two representations is `128`. -/
theorem fourthR14n_pair : pairTriGMO 32 88 false fourthR14nL fourthR14nW fourthR14nHX fourthR14nGX
    ((tensorWordDenAll fourthR14nH : ℚ) * 1) ((tensorWordDenAll fourthR14nG : ℚ) * fourthR14nSD) =
      128 := by
  unfold pairTriGMO
  rw [fourthR14n_pmat, fourthR14n_pshort, fourthR14n_podd, show (!false) = true from rfl]
  rw [fourthR14n_ptdot, fourthR14n_dens.1, fourthR14n_dens.2]
  norm_num

/-- The Fourth identification `R14n`. -/
theorem fourthR14n_ident : sExtra.symm (rhoLocal (identWordLocal fourthR14nH)
    (generatedAxisGlobalTwelveRepresentative 3)) =
      rhoLocal (identWordLocal fourthR14nG) (generatedAxisGlobalTwelveRepresentative 5) :=
  ident_inverse_GMO 3 5 _ _ fourthR14nL fourthR14nW
    (ofList_ok fourthR14nHT fourthR14nT_labels.1) (ofList_ok fourthR14nGT fourthR14nT_labels.2)
    rfl rfl fourthR14nHX_bnd fourthR14nGX_bnd (by norm_num) (by norm_num) fourthR14nL_actual fourthR14nW_actual fourthR14n_pair

/-- The inverse identification at the translated root word of root 14. -/
theorem fourthR14n_inverse : FourthIdentInverse (generatedAxisGlobalTwelveFourthRootWords 14) :=
  ⟨5, _, fourthR14n_ident⟩

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
