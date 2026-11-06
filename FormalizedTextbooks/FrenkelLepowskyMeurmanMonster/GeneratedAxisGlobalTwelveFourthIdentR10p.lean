/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR10pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR10pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR10pPC

/-! # The Fourth identification `R10p` (Sixth target)

The exact pairing `pairTriGMO` of the two representations of
`GeneratedAxisGlobalTwelveFourthIdentR10pChecks` is the sum of the parts evaluated in
`...R10pPA` (matrix and short parts), `...R10pPB` (odd-short-to-tensor part) and `...R10pPC`
(tensor part); it is `128`, so the triality image of the Fourth image is the Sixth image
(`ident_forward_GMO`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The exact pairing of the two representations is `128`. -/
theorem fourthR10p_pair : pairTriGMO 32 88 true fourthR10pL fourthR10pW fourthR10pHX fourthR10pGX
    ((tensorWordDenAll fourthR10pH : ℚ) * 1) ((tensorWordDenAll fourthR10pG : ℚ) * fourthR10pSD) =
      128 := by
  unfold pairTriGMO
  rw [fourthR10p_pmat, fourthR10p_pshort, fourthR10p_podd, show (!true) = false from rfl]
  rw [fourthR10p_ptdot, fourthR10p_dens.1, fourthR10p_dens.2]
  norm_num

/-- The Fourth identification `R10p`. -/
theorem fourthR10p_ident : sExtra (rhoLocal (identWordLocal fourthR10pH)
    (generatedAxisGlobalTwelveRepresentative 3)) =
      rhoLocal (identWordLocal fourthR10pG) (generatedAxisGlobalTwelveRepresentative 5) :=
  ident_forward_GMO 3 5 _ _ fourthR10pL fourthR10pW
    (ofList_ok fourthR10pHT fourthR10pT_labels.1) (ofList_ok fourthR10pGT fourthR10pT_labels.2)
    rfl rfl fourthR10pHX_bnd fourthR10pGX_bnd (by norm_num) (by norm_num) fourthR10pL_actual fourthR10pW_actual fourthR10p_pair

/-- The forward identification at the translated root word of root 10. -/
theorem fourthR10p_forward : FourthIdentForward (generatedAxisGlobalTwelveFourthRootWords 10) :=
  ⟨5, _, fourthR10p_ident⟩

/-- Root 10 of the Fourth forest: both triality images lie in the twelve local orbits. -/
theorem fourth_root10_bound :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 10) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 10) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  fourth_merged_forward 9 fourthR10p_forward

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
