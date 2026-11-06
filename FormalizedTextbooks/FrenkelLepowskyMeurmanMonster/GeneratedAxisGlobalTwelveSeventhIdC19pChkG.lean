/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC19pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Checks of the target side of the identification Seventh cell record S7c19+ (gforest:S7c19+,
e = 1)

Letter data, composite mask data and the transport of the literal source short block onto the
literal target list of the target image are certified in the kernel. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target word. -/
def s7c19pG : List IdentLetter := s7c19pGW.map Prod.fst

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem s7c19pG_check : s7c19pGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word are packed. -/
theorem s7c19pGD_ok : s7c19pGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem s7c19pGD_cols : ∀ i : Fin 24, qmWordP (s7c19pGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 s7c19pGD.colsP i.val, s7c19pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem s7c19pGD_rows : ∀ i : Fin 24,
    fld 24 s7c19pGD.rowsP i.val = rowsOf (fun j => fld 24 s7c19pGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the short block of the target image, piece `0` (7168 terms). -/
theorem s7c19pGT_p0 : shortCheckF s7c19pGD ((seventhSrcVecG 72).sh.flat.take 7168) (s7c19pGT.take
    7168) = true :=
  shortCheckPk_sound _ 10 7 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport of the short block of the target image, piece `1` (7168 terms). -/
theorem s7c19pGT_p1 : shortCheckF s7c19pGD (((seventhSrcVecG 72).sh.flat.drop 7168).take 7168)
    ((s7c19pGT.drop 7168).take 7168) = true :=
  shortCheckPk_sound _ 10 7 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport of the short block of the target image, piece `2` (7168 terms). -/
theorem s7c19pGT_p2 : shortCheckF s7c19pGD ((((seventhSrcVecG 72).sh.flat.drop 7168).drop
    7168).take 7168) (((s7c19pGT.drop 7168).drop 7168).take 7168) = true :=
  shortCheckPk_sound _ 10 7 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport of the short block of the target image, piece `3` (6120 terms). -/
theorem s7c19pGT_p3 : shortCheckF s7c19pGD ((((seventhSrcVecG 72).sh.flat.drop 7168).drop
    7168).drop 7168) (((s7c19pGT.drop 7168).drop 7168).drop 7168) = true :=
  shortCheckPk_sound _ 10 6 _ _ (by decide +kernel)

/-- The short block of the target image is transported onto the literal targets. -/
theorem s7c19pGT_check : shortCheckF s7c19pGD (seventhSrcVecG 72).sh.flat s7c19pGT = true :=
  (shortCheckF_split _ 7168 _ _ s7c19pGT_p0 (shortCheckF_split _ 7168 _ _ s7c19pGT_p1
      (shortCheckF_split _ 7168 _ _ s7c19pGT_p2 s7c19pGT_p3)))

set_option maxRecDepth 100000 in
/-- The target list has valid labels. -/
theorem s7c19pGT_labels : s7c19pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the target word. -/
theorem s7c19pG_growth : tensorWordGrowthAll s7c19pG * (4 * (16777216 * 8) + 276 * 6144) =
    72285192944877568 := by decide

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
