/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC16pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Checks of the target side of the identification Seventh cell record S7c16+ (gforest:S7c16+,
e = 1)

Letter data, composite mask data and the transport of the literal source short block onto the
literal target list of the target image are certified in the kernel. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target word. -/
def s7c16pG : List IdentLetter := s7c16pGW.map Prod.fst

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem s7c16pG_check : s7c16pGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word are packed. -/
theorem s7c16pGD_ok : s7c16pGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem s7c16pGD_cols : ∀ i : Fin 24, qmWordP (s7c16pGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 s7c16pGD.colsP i.val, s7c16pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem s7c16pGD_rows : ∀ i : Fin 24,
    fld 24 s7c16pGD.rowsP i.val = rowsOf (fun j => fld 24 s7c16pGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the short block of the target image, piece `0` (7168 terms). -/
theorem s7c16pGT_p0 : shortCheckF s7c16pGD (srcRootEightCShort.flat.take 7168) (s7c16pGT.take
    7168) = true :=
  shortCheckPk_sound _ 10 7 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport of the short block of the target image, piece `1` (7168 terms). -/
theorem s7c16pGT_p1 : shortCheckF s7c16pGD ((srcRootEightCShort.flat.drop 7168).take 7168)
    ((s7c16pGT.drop 7168).take 7168) = true :=
  shortCheckPk_sound _ 10 7 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport of the short block of the target image, piece `2` (7168 terms). -/
theorem s7c16pGT_p2 : shortCheckF s7c16pGD (((srcRootEightCShort.flat.drop 7168).drop 7168).take
    7168) (((s7c16pGT.drop 7168).drop 7168).take 7168) = true :=
  shortCheckPk_sound _ 10 7 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport of the short block of the target image, piece `3` (7168 terms). -/
theorem s7c16pGT_p3 : shortCheckF s7c16pGD ((((srcRootEightCShort.flat.drop 7168).drop 7168).drop
    7168).take 7168) ((((s7c16pGT.drop 7168).drop 7168).drop 7168).take 7168) = true :=
  shortCheckPk_sound _ 10 7 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport of the short block of the target image, piece `4` (4904 terms). -/
theorem s7c16pGT_p4 : shortCheckF s7c16pGD ((((srcRootEightCShort.flat.drop 7168).drop 7168).drop
    7168).drop 7168) ((((s7c16pGT.drop 7168).drop 7168).drop 7168).drop 7168) = true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

/-- The short block of the target image is transported onto the literal targets. -/
theorem s7c16pGT_check : shortCheckF s7c16pGD srcRootEightCShort.flat s7c16pGT = true :=
  (shortCheckF_split _ 7168 _ _ s7c16pGT_p0 (shortCheckF_split _ 7168 _ _ s7c16pGT_p1
      (shortCheckF_split _ 7168 _ _ s7c16pGT_p2 (shortCheckF_split _ 7168 _ _ s7c16pGT_p3
      s7c16pGT_p4))))

set_option maxRecDepth 100000 in
/-- The target list has valid labels. -/
theorem s7c16pGT_labels : s7c16pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the target word. -/
theorem s7c16pG_growth : tensorWordGrowthAll s7c16pG * 15 = 7864320 := by decide

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
