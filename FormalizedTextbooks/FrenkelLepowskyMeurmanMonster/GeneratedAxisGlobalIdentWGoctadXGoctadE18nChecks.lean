/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGoctadE18nChecksL

/-! # Factory checks (target side) of the identification Eighth[23]- <-> Tenth[58]- (record
goctad:E18-, e = -1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wGoctadXGoctadE18nG_check : wGoctadXGoctadE18nGW.all (fun p => identLetterCheckP p.1 p.2)
    = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wGoctadXGoctadE18nGD_cols : ∀ i : Fin 24, qmWordP (wGoctadXGoctadE18nGW.map Prod.snd) (2 ^
    i.val, false) =
    (fld 24 wGoctadXGoctadE18nGD.colsP i.val, wGoctadXGoctadE18nGD.coeff.testBit i.val) := by
        decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wGoctadXGoctadE18nGD_rows : ∀ i : Fin 24,
    fld 24 wGoctadXGoctadE18nGD.rowsP i.val = rowsOf (fun j => fld 24 wGoctadXGoctadE18nGD.colsP
        j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 0). -/
theorem wGoctadXGoctadE18nGT_check0 :
    shortCheckPk wGoctadXGoctadE18nGD 10 15 ((srcTenthCShort.flat).take 15360)
        ((wGoctadXGoctadE18nGT).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 1). -/
theorem wGoctadXGoctadE18nGT_check1 :
    shortCheckPk wGoctadXGoctadE18nGD 10 15 (((srcTenthCShort.flat).drop 15360).take 15360)
        (((wGoctadXGoctadE18nGT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 2). -/
theorem wGoctadXGoctadE18nGT_check2 :
    shortCheckPk wGoctadXGoctadE18nGD 10 15 ((((srcTenthCShort.flat).drop 15360).drop 15360).take
        15360) ((((wGoctadXGoctadE18nGT).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 3). -/
theorem wGoctadXGoctadE18nGT_check3 :
    shortCheckPk wGoctadXGoctadE18nGD 10 1 ((((srcTenthCShort.flat).drop 15360).drop 15360).drop
        15360) ((((wGoctadXGoctadE18nGT).drop 15360).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the target image is transported onto the literal targets. -/
theorem wGoctadXGoctadE18nGT_check : shortCheckF wGoctadXGoctadE18nGD srcTenthCShort.flat
    wGoctadXGoctadE18nGT = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGoctadXGoctadE18nGT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGoctadXGoctadE18nGT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGoctadXGoctadE18nGT_check2)
    (shortCheckPk_sound _ 10 1 _ _ wGoctadXGoctadE18nGT_check3)))

/-- The coordinates of the target image. -/
theorem wGoctadXGoctadE18nW_actual : griessConwayEncode (rhoLocal (identWordLocal
    wGoctadXGoctadE18nG)
    (generatedAxisGlobalTwelveRepresentative 11)) = wGoctadXGoctadE18nW.real := by
  have hT := (tensorPlanF_actual wGoctadXGoctadE18nGPlan wGoctadXGoctadE18nGPlan_ok
      (tenthSrcXL_bnd (w := 64) (by norm_num))
    (by rw [wGoctadXGoctadE18nGPlan_word, wGoctadXGoctadE18nG_growth]; norm_num) 32).2
  rw [wGoctadXGoctadE18nGPlan_word] at hT
  exact IdentVec.word_actual (tenthSrcVecL 64) wGoctadXGoctadE18nGW wGoctadXGoctadE18nG_check
      wGoctadXGoctadE18nGD wGoctadXGoctadE18nD_ok.2 wGoctadXGoctadE18nGD_cols
    wGoctadXGoctadE18nGD_rows wGoctadXGoctadE18nGT wGoctadXGoctadE18nGT_check _ hT _
        (tenthSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
