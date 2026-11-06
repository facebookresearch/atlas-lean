/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS7c17nChecksL

/-! # Factory checks (target side) of the identification Seventh[26]- <-> Tenth[66]+ (record
gforest:S7c17-, e = -1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wGoctadXGforestS7c17nG_check : wGoctadXGforestS7c17nGW.all (fun p => identLetterCheckP p.1
    p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wGoctadXGforestS7c17nGD_cols : ∀ i : Fin 24, qmWordP (wGoctadXGforestS7c17nGW.map
    Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGoctadXGforestS7c17nGD.colsP i.val, wGoctadXGforestS7c17nGD.coeff.testBit i.val) :=
        by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wGoctadXGforestS7c17nGD_rows : ∀ i : Fin 24,
    fld 24 wGoctadXGforestS7c17nGD.rowsP i.val = rowsOf (fun j => fld 24
        wGoctadXGforestS7c17nGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 0). -/
theorem wGoctadXGforestS7c17nGT_check0 :
    shortCheckPk wGoctadXGforestS7c17nGD 10 15 ((srcTenthCShort.flat).take 15360)
        ((wGoctadXGforestS7c17nGT).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 1). -/
theorem wGoctadXGforestS7c17nGT_check1 :
    shortCheckPk wGoctadXGforestS7c17nGD 10 15 (((srcTenthCShort.flat).drop 15360).take 15360)
        (((wGoctadXGforestS7c17nGT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 2). -/
theorem wGoctadXGforestS7c17nGT_check2 :
    shortCheckPk wGoctadXGforestS7c17nGD 10 15 ((((srcTenthCShort.flat).drop 15360).drop
        15360).take 15360) ((((wGoctadXGforestS7c17nGT).drop 15360).drop 15360).take 15360) = true
        := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 3). -/
theorem wGoctadXGforestS7c17nGT_check3 :
    shortCheckPk wGoctadXGforestS7c17nGD 10 1 ((((srcTenthCShort.flat).drop 15360).drop
        15360).drop 15360) ((((wGoctadXGforestS7c17nGT).drop 15360).drop 15360).drop 15360) = true
        := by
  decide +kernel

/-- The short block of the target image is transported onto the literal targets. -/
theorem wGoctadXGforestS7c17nGT_check : shortCheckF wGoctadXGforestS7c17nGD srcTenthCShort.flat
    wGoctadXGforestS7c17nGT = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGoctadXGforestS7c17nGT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGoctadXGforestS7c17nGT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGoctadXGforestS7c17nGT_check2)
    (shortCheckPk_sound _ 10 1 _ _ wGoctadXGforestS7c17nGT_check3)))

/-- The coordinates of the target image. -/
theorem wGoctadXGforestS7c17nW_actual : griessConwayEncode (rhoLocal (identWordLocal
    wGoctadXGforestS7c17nG)
    (generatedAxisGlobalTwelveRepresentative 11)) = wGoctadXGforestS7c17nW.real := by
  have hT := (tensorPlanF_actual wGoctadXGforestS7c17nGPlan wGoctadXGforestS7c17nGPlan_ok
      (tenthSrcXL_bnd (w := 64) (by norm_num))
    (by rw [wGoctadXGforestS7c17nGPlan_word, wGoctadXGforestS7c17nG_growth]; norm_num) 32).2
  rw [wGoctadXGforestS7c17nGPlan_word] at hT
  exact IdentVec.word_actual (tenthSrcVecL 64) wGoctadXGforestS7c17nGW
      wGoctadXGforestS7c17nG_check wGoctadXGforestS7c17nGD wGoctadXGforestS7c17nD_ok.2
      wGoctadXGforestS7c17nGD_cols
    wGoctadXGforestS7c17nGD_rows wGoctadXGforestS7c17nGT wGoctadXGforestS7c17nGT_check _ hT _
        (tenthSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
