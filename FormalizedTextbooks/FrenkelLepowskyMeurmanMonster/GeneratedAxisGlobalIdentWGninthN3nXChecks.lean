/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN3nXChecksL

/-! # Factory checks (target side) of the identification Ninth[5]- <-> Twelfth[31]+ (record
gninth:N3-, e = -1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wGninthN3nXG_check : wGninthN3nXGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wGninthN3nXGD_cols : ∀ i : Fin 24, qmWordP (wGninthN3nXGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGninthN3nXGD.colsP i.val, wGninthN3nXGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wGninthN3nXGD_rows : ∀ i : Fin 24,
    fld 24 wGninthN3nXGD.rowsP i.val = rowsOf (fun j => fld 24 wGninthN3nXGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 0). -/
theorem wGninthN3nXGT_check0 :
    shortCheckPk wGninthN3nXGD 10 15 ((twelfthShS.flat).take 15360) ((wGninthN3nXGT).take 15360) =
        true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 1). -/
theorem wGninthN3nXGT_check1 :
    shortCheckPk wGninthN3nXGD 10 15 (((twelfthShS.flat).drop 15360).take 15360)
        (((wGninthN3nXGT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 2). -/
theorem wGninthN3nXGT_check2 :
    shortCheckPk wGninthN3nXGD 10 15 ((((twelfthShS.flat).drop 15360).drop 15360).take 15360)
        ((((wGninthN3nXGT).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 3). -/
theorem wGninthN3nXGT_check3 :
    shortCheckPk wGninthN3nXGD 10 1 ((((twelfthShS.flat).drop 15360).drop 15360).drop 15360)
        ((((wGninthN3nXGT).drop 15360).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the target image is transported onto the literal targets. -/
theorem wGninthN3nXGT_check : shortCheckF wGninthN3nXGD twelfthShS.flat wGninthN3nXGT = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN3nXGT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN3nXGT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN3nXGT_check2)
    (shortCheckPk_sound _ 10 1 _ _ wGninthN3nXGT_check3)))

/-- The coordinates of the target image. -/
theorem wGninthN3nXW_actual : griessConwayEncode (rhoLocal (identWordLocal wGninthN3nXG)
    (generatedAxisGlobalTwelveRepresentative 10)) = wGninthN3nXW.real := by
  have hT := (tensorPlanF_actual wGninthN3nXGPlan wGninthN3nXGPlan_ok (twelfthSrcXW_bnd (w := 64)
      (by norm_num))
    (by rw [wGninthN3nXGPlan_word, wGninthN3nXG_growth]; norm_num) 32).2
  rw [wGninthN3nXGPlan_word] at hT
  exact IdentVec.word_actual (twelfthSrcVecS 64) wGninthN3nXGW wGninthN3nXG_check wGninthN3nXGD
      wGninthN3nXD_ok.2 wGninthN3nXGD_cols
    wGninthN3nXGD_rows wGninthN3nXGT wGninthN3nXGT_check _ hT _ (twelfthSrcS_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
