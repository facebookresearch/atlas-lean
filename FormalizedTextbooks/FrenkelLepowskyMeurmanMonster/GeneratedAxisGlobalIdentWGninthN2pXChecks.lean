/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN2pXChecksL

/-! # Factory checks (target side) of the identification Ninth[3]+ <-> Tenth[50]+ (record
gninth:N2+, e = 1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wGninthN2pXG_check : wGninthN2pXGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wGninthN2pXGD_cols : ∀ i : Fin 24, qmWordP (wGninthN2pXGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGninthN2pXGD.colsP i.val, wGninthN2pXGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wGninthN2pXGD_rows : ∀ i : Fin 24,
    fld 24 wGninthN2pXGD.rowsP i.val = rowsOf (fun j => fld 24 wGninthN2pXGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 0). -/
theorem wGninthN2pXGT_check0 :
    shortCheckPk wGninthN2pXGD 10 15 ((srcTenthCShort.flat).take 15360) ((wGninthN2pXGT).take
        15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 1). -/
theorem wGninthN2pXGT_check1 :
    shortCheckPk wGninthN2pXGD 10 15 (((srcTenthCShort.flat).drop 15360).take 15360)
        (((wGninthN2pXGT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 2). -/
theorem wGninthN2pXGT_check2 :
    shortCheckPk wGninthN2pXGD 10 15 ((((srcTenthCShort.flat).drop 15360).drop 15360).take 15360)
        ((((wGninthN2pXGT).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 3). -/
theorem wGninthN2pXGT_check3 :
    shortCheckPk wGninthN2pXGD 10 1 ((((srcTenthCShort.flat).drop 15360).drop 15360).drop 15360)
        ((((wGninthN2pXGT).drop 15360).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the target image is transported onto the literal targets. -/
theorem wGninthN2pXGT_check : shortCheckF wGninthN2pXGD srcTenthCShort.flat wGninthN2pXGT = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN2pXGT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN2pXGT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN2pXGT_check2)
    (shortCheckPk_sound _ 10 1 _ _ wGninthN2pXGT_check3)))

/-- The coordinates of the target image. -/
theorem wGninthN2pXW_actual : griessConwayEncode (rhoLocal (identWordLocal wGninthN2pXG)
    (generatedAxisGlobalTwelveRepresentative 11)) = wGninthN2pXW.real := by
  have hT := (tensorPlanF_actual wGninthN2pXGPlan wGninthN2pXGPlan_ok (tenthSrcXL_bnd (w := 64)
      (by norm_num))
    (by rw [wGninthN2pXGPlan_word, wGninthN2pXG_growth]; norm_num) 32).2
  rw [wGninthN2pXGPlan_word] at hT
  exact IdentVec.word_actual (tenthSrcVecL 64) wGninthN2pXGW wGninthN2pXG_check wGninthN2pXGD
      wGninthN2pXD_ok.2 wGninthN2pXGD_cols
    wGninthN2pXGD_rows wGninthN2pXGT wGninthN2pXGT_check _ hT _ (tenthSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
