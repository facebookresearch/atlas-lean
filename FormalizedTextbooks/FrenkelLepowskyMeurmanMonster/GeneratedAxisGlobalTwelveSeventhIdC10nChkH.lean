/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC10nData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Checks of the source side of the identification Seventh cell record S7c10- (gforest:S7c10-,
e = -1)

Letter data, composite mask data and the transport of the literal source short block onto the
literal target list of the source image are certified in the kernel. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def s7c10nH : List IdentLetter := s7c10nHW.map Prod.fst

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem s7c10nH_check : s7c10nHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word are packed. -/
theorem s7c10nHD_ok : s7c10nHD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem s7c10nHD_cols : ∀ i : Fin 24, qmWordP (s7c10nHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 s7c10nHD.colsP i.val, s7c10nHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem s7c10nHD_rows : ∀ i : Fin 24,
    fld 24 s7c10nHD.rowsP i.val = rowsOf (fun j => fld 24 s7c10nHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the short block of the source image, piece `0` (7168 terms). -/
theorem s7c10nHT_p0 : shortCheckF s7c10nHD ((seventhSrcVecG 64).sh.flat.take 7168) (s7c10nHT.take
    7168) = true :=
  shortCheckPk_sound _ 10 7 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport of the short block of the source image, piece `1` (7168 terms). -/
theorem s7c10nHT_p1 : shortCheckF s7c10nHD (((seventhSrcVecG 64).sh.flat.drop 7168).take 7168)
    ((s7c10nHT.drop 7168).take 7168) = true :=
  shortCheckPk_sound _ 10 7 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport of the short block of the source image, piece `2` (7168 terms). -/
theorem s7c10nHT_p2 : shortCheckF s7c10nHD ((((seventhSrcVecG 64).sh.flat.drop 7168).drop
    7168).take 7168) (((s7c10nHT.drop 7168).drop 7168).take 7168) = true :=
  shortCheckPk_sound _ 10 7 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport of the short block of the source image, piece `3` (6120 terms). -/
theorem s7c10nHT_p3 : shortCheckF s7c10nHD ((((seventhSrcVecG 64).sh.flat.drop 7168).drop
    7168).drop 7168) (((s7c10nHT.drop 7168).drop 7168).drop 7168) = true :=
  shortCheckPk_sound _ 10 6 _ _ (by decide +kernel)

/-- The short block of the source image is transported onto the literal targets. -/
theorem s7c10nHT_check : shortCheckF s7c10nHD (seventhSrcVecG 64).sh.flat s7c10nHT = true :=
  (shortCheckF_split _ 7168 _ _ s7c10nHT_p0 (shortCheckF_split _ 7168 _ _ s7c10nHT_p1
      (shortCheckF_split _ 7168 _ _ s7c10nHT_p2 s7c10nHT_p3)))

set_option maxRecDepth 100000 in
/-- The target list has valid labels. -/
theorem s7c10nHT_labels : s7c10nHT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem s7c10nH_growth : tensorWordGrowthAll s7c10nH * (4 * (16777216 * 8) + 276 * 6144) =
    9035649118109696 := by decide

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
