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

/-! # Checks of the target side of the identification Seventh cell record S7c10- (gforest:S7c10-,
e = -1)

Letter data, composite mask data and the transport of the literal source short block onto the
literal target list of the target image are certified in the kernel. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target word. -/
def s7c10nG : List IdentLetter := s7c10nGW.map Prod.fst

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem s7c10nG_check : s7c10nGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word are packed. -/
theorem s7c10nGD_ok : s7c10nGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem s7c10nGD_cols : ∀ i : Fin 24, qmWordP (s7c10nGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 s7c10nGD.colsP i.val, s7c10nGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem s7c10nGD_rows : ∀ i : Fin 24,
    fld 24 s7c10nGD.rowsP i.val = rowsOf (fun j => fld 24 s7c10nGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the short block of the target image, piece `0` (7168 terms). -/
theorem s7c10nGT_p0 : shortCheckF s7c10nGD (srcRootEightCShort.flat.take 7168) (s7c10nGT.take
    7168) = true :=
  shortCheckPk_sound _ 10 7 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport of the short block of the target image, piece `1` (7168 terms). -/
theorem s7c10nGT_p1 : shortCheckF s7c10nGD ((srcRootEightCShort.flat.drop 7168).take 7168)
    ((s7c10nGT.drop 7168).take 7168) = true :=
  shortCheckPk_sound _ 10 7 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport of the short block of the target image, piece `2` (7168 terms). -/
theorem s7c10nGT_p2 : shortCheckF s7c10nGD (((srcRootEightCShort.flat.drop 7168).drop 7168).take
    7168) (((s7c10nGT.drop 7168).drop 7168).take 7168) = true :=
  shortCheckPk_sound _ 10 7 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport of the short block of the target image, piece `3` (7168 terms). -/
theorem s7c10nGT_p3 : shortCheckF s7c10nGD ((((srcRootEightCShort.flat.drop 7168).drop 7168).drop
    7168).take 7168) ((((s7c10nGT.drop 7168).drop 7168).drop 7168).take 7168) = true :=
  shortCheckPk_sound _ 10 7 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport of the short block of the target image, piece `4` (4904 terms). -/
theorem s7c10nGT_p4 : shortCheckF s7c10nGD ((((srcRootEightCShort.flat.drop 7168).drop 7168).drop
    7168).drop 7168) ((((s7c10nGT.drop 7168).drop 7168).drop 7168).drop 7168) = true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

/-- The short block of the target image is transported onto the literal targets. -/
theorem s7c10nGT_check : shortCheckF s7c10nGD srcRootEightCShort.flat s7c10nGT = true :=
  (shortCheckF_split _ 7168 _ _ s7c10nGT_p0 (shortCheckF_split _ 7168 _ _ s7c10nGT_p1
      (shortCheckF_split _ 7168 _ _ s7c10nGT_p2 (shortCheckF_split _ 7168 _ _ s7c10nGT_p3
      s7c10nGT_p4))))

set_option maxRecDepth 100000 in
/-- The target list has valid labels. -/
theorem s7c10nGT_labels : s7c10nGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the target word. -/
theorem s7c10nG_growth : tensorWordGrowthAll s7c10nG * 15 = 2013265920 := by decide

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
