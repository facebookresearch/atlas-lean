/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV11pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV11pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV11pPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthIdent

/-! # The Tenth identification T11+ (gtenth)

All parts of the exact pairing (`pairTriGMZ_parts`, values checked in the kernel) sum to the Griess
norm `128`, so the triality image of the source image is the target image (`ident_forward_GMZ`);
    restated as
`GeneratedAxisGlobalTwelveTenthIdentPos 11 11` for
    `GeneratedAxisGlobalTwelveTenthPureIdentified_of_transporters`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The exact pairing of the triality image of the source image with the target image. -/
theorem tv11p_pair : pairTriGMZ 32 64 true tv11pL tv11pW tv11pHX tv11pGX ((tensorWordDenAll tv11pH
    : ℚ) * 32 / 2 ^ 12) ((tensorWordDenAll tv11pG : ℚ) * 32 / 2 ^ 13) = 128 := by
  rw [pairTriGMZ_parts tv11p_hok tv11p_hm tv11p_hp tv11p_hn tv11p_ha tv11p_hb tv11p_hc,
      tv11pH_den, tv11pG_den]
  norm_num [tv11pL, tv11pW]

/-- The identification T11+ (gtenth): the triality image of the source image is the target image. -/
theorem tv11p_ident : sExtra (rhoLocal (identWordLocal tv11pH)
    (generatedAxisGlobalTwelveRepresentative 11)) =
    rhoLocal (identWordLocal tv11pG) (generatedAxisGlobalTwelveRepresentative 11) :=
  ident_forward_GMZ 11 11 _ _ tv11pL tv11pW (ofList_ok tv11pHT tv11pHT_labels) (ofList_ok tv11pGT
      tv11pGT_labels) rfl rfl
    tv11pH_tensor.1 tv11pG_tensor.1 (by norm_num) (by norm_num) tv11pL_actual tv11pW_actual
        tv11p_pair

/-- The Tenth identification at root word 11 with the numerically found prefix (target root 11). -/
theorem generatedAxisGlobalTwelveTenthIdent11p : GeneratedAxisGlobalTwelveTenthIdentPos 11 11
    generatedAxisGlobalTwelveTenthPrefix11p := by
  have h1 : generatedAxisGlobalTwelveTenthRootIdent 11 = tv11pH := rfl
  have h2 : generatedAxisGlobalTwelveTenthPrefix11p ++ generatedAxisGlobalTwelveTenthRootIdent 11
      = tv11pG := rfl
  unfold GeneratedAxisGlobalTwelveTenthIdentPos
  rw [h2, h1]
  exact tv11p_ident

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
