/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV59pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV59pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV59pPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthIdent

/-! # The Tenth identification T59+ (gtenth)

All parts of the exact pairing (`pairTriGMZ_parts`, values checked in the kernel) sum to the Griess
norm `128`, so the triality image of the source image is the target image (`ident_forward_GMZ`);
    restated as
`GeneratedAxisGlobalTwelveTenthIdentPos 59 59` for
    `GeneratedAxisGlobalTwelveTenthPureIdentified_of_transporters`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The exact pairing of the triality image of the source image with the target image. -/
theorem tv59p_pair : pairTriGMZ 32 64 true tv59pL tv59pW tv59pHX tv59pGX ((tensorWordDenAll tv59pH
    : ℚ) * 32 / 2 ^ 12) ((tensorWordDenAll tv59pG : ℚ) * 32 / 2 ^ 13) = 128 := by
  rw [pairTriGMZ_parts tv59p_hok tv59p_hm tv59p_hp tv59p_hn tv59p_ha tv59p_hb tv59p_hc,
      tv59pH_den, tv59pG_den]
  norm_num [tv59pL, tv59pW]

/-- The identification T59+ (gtenth): the triality image of the source image is the target image. -/
theorem tv59p_ident : sExtra (rhoLocal (identWordLocal tv59pH)
    (generatedAxisGlobalTwelveRepresentative 11)) =
    rhoLocal (identWordLocal tv59pG) (generatedAxisGlobalTwelveRepresentative 11) :=
  ident_forward_GMZ 11 11 _ _ tv59pL tv59pW (ofList_ok tv59pHT tv59pHT_labels) (ofList_ok tv59pGT
      tv59pGT_labels) rfl rfl
    tv59pH_tensor.1 tv59pG_tensor.1 (by norm_num) (by norm_num) tv59pL_actual tv59pW_actual
        tv59p_pair

/-- The Tenth identification at root word 59 with the numerically found prefix (target root 59). -/
theorem generatedAxisGlobalTwelveTenthIdent59p : GeneratedAxisGlobalTwelveTenthIdentPos 59 59
    generatedAxisGlobalTwelveTenthPrefix59p := by
  have h1 : generatedAxisGlobalTwelveTenthRootIdent 59 = tv59pH := rfl
  have h2 : generatedAxisGlobalTwelveTenthPrefix59p ++ generatedAxisGlobalTwelveTenthRootIdent 59
      = tv59pG := rfl
  unfold GeneratedAxisGlobalTwelveTenthIdentPos
  rw [h2, h1]
  exact tv59p_ident

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
