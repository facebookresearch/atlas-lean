/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthIdC6pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Checks of the source side of the identification Sixth cell record S6c6+ (gforest:S6c6+, e = 1)

Letter data, composite mask data and the transport of the literal source short block onto the
literal target list of the source image are certified in the kernel. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def s6c6pH : List IdentLetter := s6c6pHW.map Prod.fst

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem s6c6pH_check : s6c6pHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word are packed. -/
theorem s6c6pHD_ok : s6c6pHD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem s6c6pHD_cols : ∀ i : Fin 24, qmWordP (s6c6pHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 s6c6pHD.colsP i.val, s6c6pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem s6c6pHD_rows : ∀ i : Fin 24,
    fld 24 s6c6pHD.rowsP i.val = rowsOf (fun j => fld 24 s6c6pHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the short block of the source image, piece `0` (7168 terms). -/
theorem s6c6pHT_p0 : shortCheckF s6c6pHD (sixthLitShort.flat.take 7168) (s6c6pHT.take 7168) = true
    :=
  shortCheckPk_sound _ 10 7 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport of the short block of the source image, piece `1` (7168 terms). -/
theorem s6c6pHT_p1 : shortCheckF s6c6pHD ((sixthLitShort.flat.drop 7168).take 7168) ((s6c6pHT.drop
    7168).take 7168) = true :=
  shortCheckPk_sound _ 10 7 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport of the short block of the source image, piece `2` (7168 terms). -/
theorem s6c6pHT_p2 : shortCheckF s6c6pHD (((sixthLitShort.flat.drop 7168).drop 7168).take 7168)
    (((s6c6pHT.drop 7168).drop 7168).take 7168) = true :=
  shortCheckPk_sound _ 10 7 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport of the short block of the source image, piece `3` (7168 terms). -/
theorem s6c6pHT_p3 : shortCheckF s6c6pHD ((((sixthLitShort.flat.drop 7168).drop 7168).drop
    7168).take 7168) ((((s6c6pHT.drop 7168).drop 7168).drop 7168).take 7168) = true :=
  shortCheckPk_sound _ 10 7 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport of the short block of the source image, piece `4` (1640 terms). -/
theorem s6c6pHT_p4 : shortCheckF s6c6pHD ((((sixthLitShort.flat.drop 7168).drop 7168).drop
    7168).drop 7168) ((((s6c6pHT.drop 7168).drop 7168).drop 7168).drop 7168) = true :=
  shortCheckPk_sound _ 10 2 _ _ (by decide +kernel)

/-- The short block of the source image is transported onto the literal targets. -/
theorem s6c6pHT_check : shortCheckF s6c6pHD sixthLitShort.flat s6c6pHT = true :=
  (shortCheckF_split _ 7168 _ _ s6c6pHT_p0 (shortCheckF_split _ 7168 _ _ s6c6pHT_p1
      (shortCheckF_split _ 7168 _ _ s6c6pHT_p2 (shortCheckF_split _ 7168 _ _ s6c6pHT_p3
      s6c6pHT_p4))))

set_option maxRecDepth 100000 in
/-- The target list has valid labels. -/
theorem s6c6pHT_labels : s6c6pHT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem s6c6pH_growth : tensorWordGrowthAll s6c6pH * (2 ^ 8 - 1) = 1095216660480 := by decide

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
