/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN6nXChecksL

/-! # Factory checks (target side) of the identification Ninth[10]- <-> Twelfth[12]- (record
gninth:N6-, e = -1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wGninthN6nXG_check : wGninthN6nXGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wGninthN6nXGD_cols : ∀ i : Fin 24, qmWordP (wGninthN6nXGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGninthN6nXGD.colsP i.val, wGninthN6nXGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wGninthN6nXGD_rows : ∀ i : Fin 24,
    fld 24 wGninthN6nXGD.rowsP i.val = rowsOf (fun j => fld 24 wGninthN6nXGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 0). -/
theorem wGninthN6nXGT_check0 :
    shortCheckPk wGninthN6nXGD 10 15 ((twelfthShS.flat).take 15360) ((wGninthN6nXGT).take 15360) =
        true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 1). -/
theorem wGninthN6nXGT_check1 :
    shortCheckPk wGninthN6nXGD 10 15 (((twelfthShS.flat).drop 15360).take 15360)
        (((wGninthN6nXGT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 2). -/
theorem wGninthN6nXGT_check2 :
    shortCheckPk wGninthN6nXGD 10 15 ((((twelfthShS.flat).drop 15360).drop 15360).take 15360)
        ((((wGninthN6nXGT).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 3). -/
theorem wGninthN6nXGT_check3 :
    shortCheckPk wGninthN6nXGD 10 1 ((((twelfthShS.flat).drop 15360).drop 15360).drop 15360)
        ((((wGninthN6nXGT).drop 15360).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the target image is transported onto the literal targets. -/
theorem wGninthN6nXGT_check : shortCheckF wGninthN6nXGD twelfthShS.flat wGninthN6nXGT = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN6nXGT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN6nXGT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN6nXGT_check2)
    (shortCheckPk_sound _ 10 1 _ _ wGninthN6nXGT_check3)))

/-- The coordinates of the target image. -/
theorem wGninthN6nXW_actual : griessConwayEncode (rhoLocal (identWordLocal wGninthN6nXG)
    (generatedAxisGlobalTwelveRepresentative 10)) = wGninthN6nXW.real := by
  have hT := (tensorPlanF_actual wGninthN6nXGPlan wGninthN6nXGPlan_ok (twelfthSrcXW_bnd (w := 64)
      (by norm_num))
    (by rw [wGninthN6nXGPlan_word, wGninthN6nXG_growth]; norm_num) 32).2
  rw [wGninthN6nXGPlan_word] at hT
  exact IdentVec.word_actual (twelfthSrcVecS 64) wGninthN6nXGW wGninthN6nXG_check wGninthN6nXGD
      wGninthN6nXD_ok.2 wGninthN6nXGD_cols
    wGninthN6nXGD_rows wGninthN6nXGT wGninthN6nXGT_check _ hT _ (twelfthSrcS_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
