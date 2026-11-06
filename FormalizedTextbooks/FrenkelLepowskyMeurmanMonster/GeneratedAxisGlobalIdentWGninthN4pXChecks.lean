/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN4pXChecksL

/-! # Factory checks (target side) of the identification Ninth[6]+ <-> Tenth[74]- (record
gninth:N4+, e = 1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wGninthN4pXG_check : wGninthN4pXGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wGninthN4pXGD_cols : ∀ i : Fin 24, qmWordP (wGninthN4pXGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGninthN4pXGD.colsP i.val, wGninthN4pXGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wGninthN4pXGD_rows : ∀ i : Fin 24,
    fld 24 wGninthN4pXGD.rowsP i.val = rowsOf (fun j => fld 24 wGninthN4pXGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 0). -/
theorem wGninthN4pXGT_check0 :
    shortCheckPk wGninthN4pXGD 10 15 ((srcTenthCShort.flat).take 15360) ((wGninthN4pXGT).take
        15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 1). -/
theorem wGninthN4pXGT_check1 :
    shortCheckPk wGninthN4pXGD 10 15 (((srcTenthCShort.flat).drop 15360).take 15360)
        (((wGninthN4pXGT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 2). -/
theorem wGninthN4pXGT_check2 :
    shortCheckPk wGninthN4pXGD 10 15 ((((srcTenthCShort.flat).drop 15360).drop 15360).take 15360)
        ((((wGninthN4pXGT).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 3). -/
theorem wGninthN4pXGT_check3 :
    shortCheckPk wGninthN4pXGD 10 1 ((((srcTenthCShort.flat).drop 15360).drop 15360).drop 15360)
        ((((wGninthN4pXGT).drop 15360).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the target image is transported onto the literal targets. -/
theorem wGninthN4pXGT_check : shortCheckF wGninthN4pXGD srcTenthCShort.flat wGninthN4pXGT = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN4pXGT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN4pXGT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN4pXGT_check2)
    (shortCheckPk_sound _ 10 1 _ _ wGninthN4pXGT_check3)))

/-- The coordinates of the target image. -/
theorem wGninthN4pXW_actual : griessConwayEncode (rhoLocal (identWordLocal wGninthN4pXG)
    (generatedAxisGlobalTwelveRepresentative 11)) = wGninthN4pXW.real := by
  have hT := (tensorPlanF_actual wGninthN4pXGPlan wGninthN4pXGPlan_ok (tenthSrcXL_bnd (w := 64)
      (by norm_num))
    (by rw [wGninthN4pXGPlan_word, wGninthN4pXG_growth]; norm_num) 32).2
  rw [wGninthN4pXGPlan_word] at hT
  exact IdentVec.word_actual (tenthSrcVecL 64) wGninthN4pXGW wGninthN4pXG_check wGninthN4pXGD
      wGninthN4pXD_ok.2 wGninthN4pXGD_cols
    wGninthN4pXGD_rows wGninthN4pXGT wGninthN4pXGT_check _ hT _ (tenthSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
