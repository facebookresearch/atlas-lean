/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC3nData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Checks of the source side of the identification Seventh cell record S7c3- (gforest:S7c3-, e
= -1)

Letter data, composite mask data and the transport of the literal source short block onto the
literal target list of the source image are certified in the kernel. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def s7c3nH : List IdentLetter := s7c3nHW.map Prod.fst

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem s7c3nH_check : s7c3nHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word are packed. -/
theorem s7c3nHD_ok : s7c3nHD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem s7c3nHD_cols : ∀ i : Fin 24, qmWordP (s7c3nHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 s7c3nHD.colsP i.val, s7c3nHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem s7c3nHD_rows : ∀ i : Fin 24,
    fld 24 s7c3nHD.rowsP i.val = rowsOf (fun j => fld 24 s7c3nHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the short block of the source image, piece `0` (7168 terms). -/
theorem s7c3nHT_p0 : shortCheckF s7c3nHD ((seventhSrcVecG 80).sh.flat.take 7168) (s7c3nHT.take
    7168) = true :=
  shortCheckPk_sound _ 10 7 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport of the short block of the source image, piece `1` (7168 terms). -/
theorem s7c3nHT_p1 : shortCheckF s7c3nHD (((seventhSrcVecG 80).sh.flat.drop 7168).take 7168)
    ((s7c3nHT.drop 7168).take 7168) = true :=
  shortCheckPk_sound _ 10 7 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport of the short block of the source image, piece `2` (7168 terms). -/
theorem s7c3nHT_p2 : shortCheckF s7c3nHD ((((seventhSrcVecG 80).sh.flat.drop 7168).drop 7168).take
    7168) (((s7c3nHT.drop 7168).drop 7168).take 7168) = true :=
  shortCheckPk_sound _ 10 7 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport of the short block of the source image, piece `3` (6120 terms). -/
theorem s7c3nHT_p3 : shortCheckF s7c3nHD ((((seventhSrcVecG 80).sh.flat.drop 7168).drop 7168).drop
    7168) (((s7c3nHT.drop 7168).drop 7168).drop 7168) = true :=
  shortCheckPk_sound _ 10 6 _ _ (by decide +kernel)

/-- The short block of the source image is transported onto the literal targets. -/
theorem s7c3nHT_check : shortCheckF s7c3nHD (seventhSrcVecG 80).sh.flat s7c3nHT = true :=
  (shortCheckF_split _ 7168 _ _ s7c3nHT_p0 (shortCheckF_split _ 7168 _ _ s7c3nHT_p1
      (shortCheckF_split _ 7168 _ _ s7c3nHT_p2 s7c3nHT_p3)))

set_option maxRecDepth 100000 in
/-- The target list has valid labels. -/
theorem s7c3nHT_labels : s7c3nHT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem s7c3nH_growth : tensorWordGrowthAll s7c3nH * (4 * (16777216 * 8) + 276 * 6144) =
    35295504367616 := by decide

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
