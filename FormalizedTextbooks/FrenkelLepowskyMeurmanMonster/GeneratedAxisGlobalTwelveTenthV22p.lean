/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV22pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV22pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV22pPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthIdent

/-! # The Tenth identification T22+ (gtenth)

All parts of the exact pairing (`pairTriGMZ_parts`, values checked in the kernel) sum to the Griess
norm `128`, so the triality image of the source image is the target image (`ident_forward_GMZ`);
    restated as
`GeneratedAxisGlobalTwelveTenthIdentPos 22 22` for
    `GeneratedAxisGlobalTwelveTenthPureIdentified_of_transporters`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The exact pairing of the triality image of the source image with the target image. -/
theorem tv22p_pair : pairTriGMZ 32 64 true tv22pL tv22pW tv22pHX tv22pGX ((tensorWordDenAll tv22pH
    : ℚ) * 32 / 2 ^ 17) ((tensorWordDenAll tv22pG : ℚ) * 32 / 2 ^ 18) = 128 := by
  rw [pairTriGMZ_parts tv22p_hok tv22p_hm tv22p_hp tv22p_hn tv22p_ha tv22p_hb tv22p_hc,
      tv22pH_den, tv22pG_den]
  norm_num [tv22pL, tv22pW]

/-- The identification T22+ (gtenth): the triality image of the source image is the target image. -/
theorem tv22p_ident : sExtra (rhoLocal (identWordLocal tv22pH)
    (generatedAxisGlobalTwelveRepresentative 11)) =
    rhoLocal (identWordLocal tv22pG) (generatedAxisGlobalTwelveRepresentative 11) :=
  ident_forward_GMZ 11 11 _ _ tv22pL tv22pW (ofList_ok tv22pHT tv22pHT_labels) (ofList_ok tv22pGT
      tv22pGT_labels) rfl rfl
    tv22pH_tensor.1 tv22pG_tensor.1 (by norm_num) (by norm_num) tv22pL_actual tv22pW_actual
        tv22p_pair

/-- The Tenth identification at root word 22 with the numerically found prefix (target root 22). -/
theorem generatedAxisGlobalTwelveTenthIdent22p : GeneratedAxisGlobalTwelveTenthIdentPos 22 22
    generatedAxisGlobalTwelveTenthPrefix22p := by
  have h1 : generatedAxisGlobalTwelveTenthRootIdent 22 = tv22pH := rfl
  have h2 : generatedAxisGlobalTwelveTenthPrefix22p ++ generatedAxisGlobalTwelveTenthRootIdent 22
      = tv22pG := rfl
  unfold GeneratedAxisGlobalTwelveTenthIdentPos
  rw [h2, h1]
  exact tv22p_ident

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
