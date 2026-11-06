/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV18nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV18nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV18nPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthIdent

/-! # The Tenth identification T18- (gtenth)

All parts of the exact pairing (`pairTriGMZ_parts`, values checked in the kernel) sum to the Griess
norm `128`, so the triality image of the source image is the target image (`ident_inverse_GMZ`);
    restated as
`GeneratedAxisGlobalTwelveTenthIdentNeg 18 18` for
    `GeneratedAxisGlobalTwelveTenthPureIdentified_of_transporters`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The exact pairing of the triality image of the source image with the target image. -/
theorem tv18n_pair : pairTriGMZ 32 64 false tv18nL tv18nW tv18nHX tv18nGX ((tensorWordDenAll
    tv18nH : ℚ) * 32 / 2 ^ 16) ((tensorWordDenAll tv18nG : ℚ) * 32 / 2 ^ 17) = 128 := by
  rw [pairTriGMZ_parts tv18n_hok tv18n_hm tv18n_hp tv18n_hn tv18n_ha tv18n_hb tv18n_hc,
      tv18nH_den, tv18nG_den]
  norm_num [tv18nL, tv18nW]

/-- The identification T18- (gtenth): the triality image of the source image is the target image. -/
theorem tv18n_ident : sExtra.symm (rhoLocal (identWordLocal tv18nH)
    (generatedAxisGlobalTwelveRepresentative 11)) =
    rhoLocal (identWordLocal tv18nG) (generatedAxisGlobalTwelveRepresentative 11) :=
  ident_inverse_GMZ 11 11 _ _ tv18nL tv18nW (ofList_ok tv18nHT tv18nHT_labels) (ofList_ok tv18nGT
      tv18nGT_labels) rfl rfl
    tv18nH_tensor.1 tv18nG_tensor.1 (by norm_num) (by norm_num) tv18nL_actual tv18nW_actual
        tv18n_pair

/-- The Tenth identification at root word 18 with the numerically found prefix (target root 18). -/
theorem generatedAxisGlobalTwelveTenthIdent18n : GeneratedAxisGlobalTwelveTenthIdentNeg 18 18
    generatedAxisGlobalTwelveTenthPrefix18n := by
  have h1 : generatedAxisGlobalTwelveTenthRootIdent 18 = tv18nH := rfl
  have h2 : generatedAxisGlobalTwelveTenthPrefix18n ++ generatedAxisGlobalTwelveTenthRootIdent 18
      = tv18nG := rfl
  unfold GeneratedAxisGlobalTwelveTenthIdentNeg
  rw [h2, h1]
  exact tv18n_ident

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
