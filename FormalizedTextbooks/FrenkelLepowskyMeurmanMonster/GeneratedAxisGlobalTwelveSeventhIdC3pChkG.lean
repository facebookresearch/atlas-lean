/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC3pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Checks of the target side of the identification Seventh cell record S7c3+ (gforest:S7c3+, e
= 1)

Letter data, composite mask data and the transport of the literal source short block onto the
literal target list of the target image are certified in the kernel. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target word. -/
def s7c3pG : List IdentLetter := s7c3pGW.map Prod.fst

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem s7c3pG_check : s7c3pGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word are packed. -/
theorem s7c3pGD_ok : s7c3pGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem s7c3pGD_cols : ∀ i : Fin 24, qmWordP (s7c3pGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 s7c3pGD.colsP i.val, s7c3pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem s7c3pGD_rows : ∀ i : Fin 24,
    fld 24 s7c3pGD.rowsP i.val = rowsOf (fun j => fld 24 s7c3pGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the short block of the target image, piece `0` (4136 terms). -/
theorem s7c3pGT_p0 : shortCheckF s7c3pGD (fifthSrcVecW 64).sh.flat s7c3pGT = true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

/-- The short block of the target image is transported onto the literal targets. -/
theorem s7c3pGT_check : shortCheckF s7c3pGD (fifthSrcVecW 64).sh.flat s7c3pGT = true :=
  s7c3pGT_p0

set_option maxRecDepth 100000 in
/-- The target list has valid labels. -/
theorem s7c3pGT_labels : s7c3pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the target word. -/
theorem s7c3pG_growth : tensorWordGrowthAll s7c3pG * 64 = 2199023255552 := by decide

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
