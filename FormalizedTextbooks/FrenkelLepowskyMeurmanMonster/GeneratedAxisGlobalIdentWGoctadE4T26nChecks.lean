/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE4T26nChecksL

/-! # Factory checks (target side) of the identification Eighth[8]- <-> Tenth[40]+ (record
goctad:E4@T26-, e = -1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wGoctadE4T26nG_check : wGoctadE4T26nGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wGoctadE4T26nGD_cols : ∀ i : Fin 24, qmWordP (wGoctadE4T26nGW.map Prod.snd) (2 ^ i.val,
    false) =
    (fld 24 wGoctadE4T26nGD.colsP i.val, wGoctadE4T26nGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wGoctadE4T26nGD_rows : ∀ i : Fin 24,
    fld 24 wGoctadE4T26nGD.rowsP i.val = rowsOf (fun j => fld 24 wGoctadE4T26nGD.colsP j.val) i :=
        by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 0). -/
theorem wGoctadE4T26nGT_check0 :
    shortCheckPk wGoctadE4T26nGD 10 15 ((srcTenthCShort.flat).take 15360) ((wGoctadE4T26nGT).take
        15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 1). -/
theorem wGoctadE4T26nGT_check1 :
    shortCheckPk wGoctadE4T26nGD 10 15 (((srcTenthCShort.flat).drop 15360).take 15360)
        (((wGoctadE4T26nGT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 2). -/
theorem wGoctadE4T26nGT_check2 :
    shortCheckPk wGoctadE4T26nGD 10 15 ((((srcTenthCShort.flat).drop 15360).drop 15360).take
        15360) ((((wGoctadE4T26nGT).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 3). -/
theorem wGoctadE4T26nGT_check3 :
    shortCheckPk wGoctadE4T26nGD 10 1 ((((srcTenthCShort.flat).drop 15360).drop 15360).drop 15360)
        ((((wGoctadE4T26nGT).drop 15360).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the target image is transported onto the literal targets. -/
theorem wGoctadE4T26nGT_check : shortCheckF wGoctadE4T26nGD srcTenthCShort.flat wGoctadE4T26nGT =
    true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGoctadE4T26nGT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGoctadE4T26nGT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGoctadE4T26nGT_check2)
    (shortCheckPk_sound _ 10 1 _ _ wGoctadE4T26nGT_check3)))

/-- The coordinates of the target image. -/
theorem wGoctadE4T26nW_actual : griessConwayEncode (rhoLocal (identWordLocal wGoctadE4T26nG)
    (generatedAxisGlobalTwelveRepresentative 11)) = wGoctadE4T26nW.real := by
  have hT := (tensorPlanF_actual wGoctadE4T26nGPlan wGoctadE4T26nGPlan_ok (tenthSrcXL_bnd (w :=
      64) (by norm_num))
    (by rw [wGoctadE4T26nGPlan_word, wGoctadE4T26nG_growth]; norm_num) 32).2
  rw [wGoctadE4T26nGPlan_word] at hT
  exact IdentVec.word_actual (tenthSrcVecL 64) wGoctadE4T26nGW wGoctadE4T26nG_check
      wGoctadE4T26nGD wGoctadE4T26nD_ok.2 wGoctadE4T26nGD_cols
    wGoctadE4T26nGD_rows wGoctadE4T26nGT wGoctadE4T26nGT_check _ hT _ (tenthSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
