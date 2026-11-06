/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN1nChecksL

/-! # Factory checks (target side) of the identification Ninth[1]- <-> Tenth[33]+ (record
gninth:N1-, e = -1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wGninthN1nG_check : wGninthN1nGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wGninthN1nGD_cols : ∀ i : Fin 24, qmWordP (wGninthN1nGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGninthN1nGD.colsP i.val, wGninthN1nGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wGninthN1nGD_rows : ∀ i : Fin 24,
    fld 24 wGninthN1nGD.rowsP i.val = rowsOf (fun j => fld 24 wGninthN1nGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 0). -/
theorem wGninthN1nGT_check0 :
    shortCheckPk wGninthN1nGD 10 15 ((srcTenthCShort.flat).take 15360) ((wGninthN1nGT).take 15360)
        = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 1). -/
theorem wGninthN1nGT_check1 :
    shortCheckPk wGninthN1nGD 10 15 (((srcTenthCShort.flat).drop 15360).take 15360)
        (((wGninthN1nGT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 2). -/
theorem wGninthN1nGT_check2 :
    shortCheckPk wGninthN1nGD 10 15 ((((srcTenthCShort.flat).drop 15360).drop 15360).take 15360)
        ((((wGninthN1nGT).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 3). -/
theorem wGninthN1nGT_check3 :
    shortCheckPk wGninthN1nGD 10 1 ((((srcTenthCShort.flat).drop 15360).drop 15360).drop 15360)
        ((((wGninthN1nGT).drop 15360).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the target image is transported onto the literal targets. -/
theorem wGninthN1nGT_check : shortCheckF wGninthN1nGD srcTenthCShort.flat wGninthN1nGT = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN1nGT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN1nGT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN1nGT_check2)
    (shortCheckPk_sound _ 10 1 _ _ wGninthN1nGT_check3)))

/-- The coordinates of the target image. -/
theorem wGninthN1nW_actual : griessConwayEncode (rhoLocal (identWordLocal wGninthN1nG)
    (generatedAxisGlobalTwelveRepresentative 11)) = wGninthN1nW.real := by
  have hT := (tensorPlanF_actual wGninthN1nGPlan wGninthN1nGPlan_ok (tenthSrcXL_bnd (w := 64) (by
      norm_num))
    (by rw [wGninthN1nGPlan_word, wGninthN1nG_growth]; norm_num) 32).2
  rw [wGninthN1nGPlan_word] at hT
  exact IdentVec.word_actual (tenthSrcVecL 64) wGninthN1nGW wGninthN1nG_check wGninthN1nGD
      wGninthN1nD_ok.2 wGninthN1nGD_cols
    wGninthN1nGD_rows wGninthN1nGT wGninthN1nGT_check _ hT _ (tenthSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
