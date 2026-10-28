/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV3pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV3pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV3pPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthIdent

/-! # The Tenth identification T3+ (gtenth)

All parts of the exact pairing (`pairTriGMZ_parts`, values checked in the kernel) sum to the Griess
norm `128`, so the triality image of the source image is the target image (`ident_forward_GMZ`);
    restated as
`GeneratedAxisGlobalTwelveTenthIdentPos 3 3` for
    `GeneratedAxisGlobalTwelveTenthPureIdentified_of_transporters`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The exact pairing of the triality image of the source image with the target image. -/
theorem tv3p_pair : pairTriGMZ 32 64 true tv3pL tv3pW tv3pHX tv3pGX ((tensorWordDenAll tv3pH : ℚ)
    * 32 / 2 ^ 16) ((tensorWordDenAll tv3pG : ℚ) * 32 / 2 ^ 17) = 128 := by
  rw [pairTriGMZ_parts tv3p_hok tv3p_hm tv3p_hp tv3p_hn tv3p_ha tv3p_hb tv3p_hc, tv3pH_den,
      tv3pG_den]
  norm_num [tv3pL, tv3pW]

/-- The identification T3+ (gtenth): the triality image of the source image is the target image. -/
theorem tv3p_ident : sExtra (rhoLocal (identWordLocal tv3pH)
    (generatedAxisGlobalTwelveRepresentative 11)) =
    rhoLocal (identWordLocal tv3pG) (generatedAxisGlobalTwelveRepresentative 11) :=
  ident_forward_GMZ 11 11 _ _ tv3pL tv3pW (ofList_ok tv3pHT tv3pHT_labels) (ofList_ok tv3pGT
      tv3pGT_labels) rfl rfl
    tv3pH_tensor.1 tv3pG_tensor.1 (by norm_num) (by norm_num) tv3pL_actual tv3pW_actual tv3p_pair

/-- The Tenth identification at root word 3 with the numerically found prefix (target root 3). -/
theorem generatedAxisGlobalTwelveTenthIdent3p : GeneratedAxisGlobalTwelveTenthIdentPos 3 3
    generatedAxisGlobalTwelveTenthPrefix3p := by
  have h1 : generatedAxisGlobalTwelveTenthRootIdent 3 = tv3pH := rfl
  have h2 : generatedAxisGlobalTwelveTenthPrefix3p ++ generatedAxisGlobalTwelveTenthRootIdent 3 =
      tv3pG := rfl
  unfold GeneratedAxisGlobalTwelveTenthIdentPos
  rw [h2, h1]
  exact tv3p_ident

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
