/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS6c4nChecksL

/-! # Factory checks (target side) of the identification Sixth[8]- <-> Tenth[73]+ (record
gforest:S6c4-, e = -1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wGoctadXGforestS6c4nG_check : wGoctadXGforestS6c4nGW.all (fun p => identLetterCheckP p.1
    p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wGoctadXGforestS6c4nGD_cols : ∀ i : Fin 24, qmWordP (wGoctadXGforestS6c4nGW.map Prod.snd)
    (2 ^ i.val, false) =
    (fld 24 wGoctadXGforestS6c4nGD.colsP i.val, wGoctadXGforestS6c4nGD.coeff.testBit i.val) := by
        decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wGoctadXGforestS6c4nGD_rows : ∀ i : Fin 24,
    fld 24 wGoctadXGforestS6c4nGD.rowsP i.val = rowsOf (fun j => fld 24
        wGoctadXGforestS6c4nGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 0). -/
theorem wGoctadXGforestS6c4nGT_check0 :
    shortCheckPk wGoctadXGforestS6c4nGD 10 15 ((srcTenthCShort.flat).take 15360)
        ((wGoctadXGforestS6c4nGT).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 1). -/
theorem wGoctadXGforestS6c4nGT_check1 :
    shortCheckPk wGoctadXGforestS6c4nGD 10 15 (((srcTenthCShort.flat).drop 15360).take 15360)
        (((wGoctadXGforestS6c4nGT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 2). -/
theorem wGoctadXGforestS6c4nGT_check2 :
    shortCheckPk wGoctadXGforestS6c4nGD 10 15 ((((srcTenthCShort.flat).drop 15360).drop
        15360).take 15360) ((((wGoctadXGforestS6c4nGT).drop 15360).drop 15360).take 15360) = true
        := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 3). -/
theorem wGoctadXGforestS6c4nGT_check3 :
    shortCheckPk wGoctadXGforestS6c4nGD 10 1 ((((srcTenthCShort.flat).drop 15360).drop 15360).drop
        15360) ((((wGoctadXGforestS6c4nGT).drop 15360).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the target image is transported onto the literal targets. -/
theorem wGoctadXGforestS6c4nGT_check : shortCheckF wGoctadXGforestS6c4nGD srcTenthCShort.flat
    wGoctadXGforestS6c4nGT = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGoctadXGforestS6c4nGT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGoctadXGforestS6c4nGT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGoctadXGforestS6c4nGT_check2)
    (shortCheckPk_sound _ 10 1 _ _ wGoctadXGforestS6c4nGT_check3)))

/-- The coordinates of the target image. -/
theorem wGoctadXGforestS6c4nW_actual : griessConwayEncode (rhoLocal (identWordLocal
    wGoctadXGforestS6c4nG)
    (generatedAxisGlobalTwelveRepresentative 11)) = wGoctadXGforestS6c4nW.real := by
  have hT := (tensorPlanF_actual wGoctadXGforestS6c4nGPlan wGoctadXGforestS6c4nGPlan_ok
      (tenthSrcXL_bnd (w := 64) (by norm_num))
    (by rw [wGoctadXGforestS6c4nGPlan_word, wGoctadXGforestS6c4nG_growth]; norm_num) 32).2
  rw [wGoctadXGforestS6c4nGPlan_word] at hT
  exact IdentVec.word_actual (tenthSrcVecL 64) wGoctadXGforestS6c4nGW wGoctadXGforestS6c4nG_check
      wGoctadXGforestS6c4nGD wGoctadXGforestS6c4nD_ok.2 wGoctadXGforestS6c4nGD_cols
    wGoctadXGforestS6c4nGD_rows wGoctadXGforestS6c4nGT wGoctadXGforestS6c4nGT_check _ hT _
        (tenthSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
