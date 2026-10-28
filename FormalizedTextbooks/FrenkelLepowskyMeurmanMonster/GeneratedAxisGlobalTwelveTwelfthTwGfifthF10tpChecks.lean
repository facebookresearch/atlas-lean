/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGfifthF10tpChecksL

/-! # Factory checks (target side) of the identification Fifth[10]+ <-> Twelfth[36]- (record
gfifth:F10t+, e = 1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem twGfifthF10tpG_check : twGfifthF10tpGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem twGfifthF10tpGD_cols : ∀ i : Fin 24, qmWordP (twGfifthF10tpGW.map Prod.snd) (2 ^ i.val,
    false) =
    (fld 24 twGfifthF10tpGD.colsP i.val, twGfifthF10tpGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem twGfifthF10tpGD_rows : ∀ i : Fin 24,
    fld 24 twGfifthF10tpGD.rowsP i.val = rowsOf (fun j => fld 24 twGfifthF10tpGD.colsP j.val) i :=
        by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 0). -/
theorem twGfifthF10tpGT_check0 :
    shortCheckPk twGfifthF10tpGD 10 15 ((twelfthShS.flat).take 15360) ((twGfifthF10tpGT).take
        15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 1). -/
theorem twGfifthF10tpGT_check1 :
    shortCheckPk twGfifthF10tpGD 10 15 (((twelfthShS.flat).drop 15360).take 15360)
        (((twGfifthF10tpGT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 2). -/
theorem twGfifthF10tpGT_check2 :
    shortCheckPk twGfifthF10tpGD 10 15 ((((twelfthShS.flat).drop 15360).drop 15360).take 15360)
        ((((twGfifthF10tpGT).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 3). -/
theorem twGfifthF10tpGT_check3 :
    shortCheckPk twGfifthF10tpGD 10 1 ((((twelfthShS.flat).drop 15360).drop 15360).drop 15360)
        ((((twGfifthF10tpGT).drop 15360).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the target image is transported onto the literal targets. -/
theorem twGfifthF10tpGT_check : shortCheckF twGfifthF10tpGD twelfthShS.flat twGfifthF10tpGT = true
    :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ twGfifthF10tpGT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ twGfifthF10tpGT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ twGfifthF10tpGT_check2)
    (shortCheckPk_sound _ 10 1 _ _ twGfifthF10tpGT_check3)))

/-- The coordinates of the target image. -/
theorem twGfifthF10tpW_actual : griessConwayEncode (rhoLocal (identWordLocal twGfifthF10tpG)
    (generatedAxisGlobalTwelveRepresentative 10)) = twGfifthF10tpW.real := by
  have hT := (tensorPlanF_actual twGfifthF10tpGPlan twGfifthF10tpGPlan_ok (twelfthSrcXW_bnd (w :=
      80) (by norm_num))
    (by rw [twGfifthF10tpGPlan_word, twGfifthF10tpG_growth]; norm_num) 32).2
  rw [twGfifthF10tpGPlan_word] at hT
  exact IdentVec.word_actual (twelfthSrcVecS 80) twGfifthF10tpGW twGfifthF10tpG_check
      twGfifthF10tpGD twGfifthF10tpD_ok.2 twGfifthF10tpGD_cols
    twGfifthF10tpGD_rows twGfifthF10tpGT twGfifthF10tpGT_check _ hT _ (twelfthSrcS_rep (by
        norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
