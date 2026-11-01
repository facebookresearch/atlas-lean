/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthIdC1nData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Checks of the target side of the identification Sixth cell record S6c1- (gforest:S6c1-, e =
-1)

Letter data, composite mask data and the transport of the literal source short block onto the
literal target list of the target image are certified in the kernel. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target word. -/
def s6c1nG : List IdentLetter := s6c1nGW.map Prod.fst

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem s6c1nG_check : s6c1nGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word are packed. -/
theorem s6c1nGD_ok : s6c1nGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem s6c1nGD_cols : ∀ i : Fin 24, qmWordP (s6c1nGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 s6c1nGD.colsP i.val, s6c1nGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem s6c1nGD_rows : ∀ i : Fin 24,
    fld 24 s6c1nGD.rowsP i.val = rowsOf (fun j => fld 24 s6c1nGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the short block of the target image, piece `0` (7168 terms). -/
theorem s6c1nGT_p0 : shortCheckF s6c1nGD ((seventhSrcVecG 64).sh.flat.take 7168) (s6c1nGT.take
    7168) = true :=
  shortCheckPk_sound _ 10 7 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport of the short block of the target image, piece `1` (7168 terms). -/
theorem s6c1nGT_p1 : shortCheckF s6c1nGD (((seventhSrcVecG 64).sh.flat.drop 7168).take 7168)
    ((s6c1nGT.drop 7168).take 7168) = true :=
  shortCheckPk_sound _ 10 7 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport of the short block of the target image, piece `2` (7168 terms). -/
theorem s6c1nGT_p2 : shortCheckF s6c1nGD ((((seventhSrcVecG 64).sh.flat.drop 7168).drop 7168).take
    7168) (((s6c1nGT.drop 7168).drop 7168).take 7168) = true :=
  shortCheckPk_sound _ 10 7 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport of the short block of the target image, piece `3` (6120 terms). -/
theorem s6c1nGT_p3 : shortCheckF s6c1nGD ((((seventhSrcVecG 64).sh.flat.drop 7168).drop 7168).drop
    7168) (((s6c1nGT.drop 7168).drop 7168).drop 7168) = true :=
  shortCheckPk_sound _ 10 6 _ _ (by decide +kernel)

/-- The short block of the target image is transported onto the literal targets. -/
theorem s6c1nGT_check : shortCheckF s6c1nGD (seventhSrcVecG 64).sh.flat s6c1nGT = true :=
  (shortCheckF_split _ 7168 _ _ s6c1nGT_p0 (shortCheckF_split _ 7168 _ _ s6c1nGT_p1
      (shortCheckF_split _ 7168 _ _ s6c1nGT_p2 s6c1nGT_p3)))

set_option maxRecDepth 100000 in
/-- The target list has valid labels. -/
theorem s6c1nGT_labels : s6c1nGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the target word. -/
theorem s6c1nG_growth : tensorWordGrowthAll s6c1nG * (4 * (16777216 * 8) + 276 * 6144) =
    282364034940928 := by decide

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
