/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR821pTChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixthF

/-! # Factory parts (octads) of the identification Root8[33]+ <-> Sixth[12]- (record r8f:R821+, e
= 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wR8fR821pT_chk : OctadDense.octSumChk 64 6 true [(wR8fR821pTHT0Labs, wR8fR821pTHT0Nums,
    2048), (wR8fR821pTHT1Labs, wR8fR821pTHT1Nums, 2048), (wR8fR821pTHT2Labs, wR8fR821pTHT2Nums,
    2048), (wR8fR821pTHT3Labs, wR8fR821pTHT3Nums, 2048), (wR8fR821pTHT4Labs, wR8fR821pTHT4Nums,
    2048), (wR8fR821pTHT5Labs, wR8fR821pTHT5Nums, 2048), (wR8fR821pTHT6Labs, wR8fR821pTHT6Nums,
    2048), (wR8fR821pTHT7Labs, wR8fR821pTHT7Nums, 2048), (wR8fR821pTHT8Labs, wR8fR821pTHT8Nums,
    2048), (wR8fR821pTHT9Labs, wR8fR821pTHT9Nums, 2048), (wR8fR821pTHT10Labs, wR8fR821pTHT10Nums,
    2048), (wR8fR821pTHT11Labs, wR8fR821pTHT11Nums, 2048), (wR8fR821pTHT12Labs,
    wR8fR821pTHT12Nums, 2048), (wR8fR821pTHT13Labs, wR8fR821pTHT13Nums, 2048),
    (wR8fR821pTHT14Labs, wR8fR821pTHT14Nums, 2048), (wR8fR821pTHT15Labs, wR8fR821pTHT15Nums,
    2048), (wR8fR821pTHT16Labs, wR8fR821pTHT16Nums, 808)] [(wR8fR821pTGT0Labs, wR8fR821pTGT0Nums,
    2048), (wR8fR821pTGT1Labs, wR8fR821pTGT1Nums, 2048), (wR8fR821pTGT2Labs, wR8fR821pTGT2Nums,
    2048), (wR8fR821pTGT3Labs, wR8fR821pTGT3Nums, 2048), (wR8fR821pTGT4Labs, wR8fR821pTGT4Nums,
    2048), (wR8fR821pTGT5Labs, wR8fR821pTGT5Nums, 2048), (wR8fR821pTGT6Labs, wR8fR821pTGT6Nums,
    2048), (wR8fR821pTGT7Labs, wR8fR821pTGT7Nums, 2048), (wR8fR821pTGT8Labs, wR8fR821pTGT8Nums,
    2048), (wR8fR821pTGT9Labs, wR8fR821pTGT9Nums, 2048), (wR8fR821pTGT10Labs, wR8fR821pTGT10Nums,
    2048), (wR8fR821pTGT11Labs, wR8fR821pTGT11Nums, 2048), (wR8fR821pTGT12Labs,
    wR8fR821pTGT12Nums, 2048), (wR8fR821pTGT13Labs, wR8fR821pTGT13Nums, 2048),
    (wR8fR821pTGT14Labs, wR8fR821pTGT14Nums, 1640)] 1007488 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wR8fR821pT_Lsh : wR8fR821pTL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR821pTHT0Labs, wR8fR821pTHT0Nums, 2048), (wR8fR821pTHT1Labs, wR8fR821pTHT1Nums, 2048),
    (wR8fR821pTHT2Labs, wR8fR821pTHT2Nums, 2048), (wR8fR821pTHT3Labs, wR8fR821pTHT3Nums, 2048),
    (wR8fR821pTHT4Labs, wR8fR821pTHT4Nums, 2048), (wR8fR821pTHT5Labs, wR8fR821pTHT5Nums, 2048),
    (wR8fR821pTHT6Labs, wR8fR821pTHT6Nums, 2048), (wR8fR821pTHT7Labs, wR8fR821pTHT7Nums, 2048),
    (wR8fR821pTHT8Labs, wR8fR821pTHT8Nums, 2048), (wR8fR821pTHT9Labs, wR8fR821pTHT9Nums, 2048),
    (wR8fR821pTHT10Labs, wR8fR821pTHT10Nums, 2048), (wR8fR821pTHT11Labs, wR8fR821pTHT11Nums,
    2048), (wR8fR821pTHT12Labs, wR8fR821pTHT12Nums, 2048), (wR8fR821pTHT13Labs,
    wR8fR821pTHT13Nums, 2048), (wR8fR821pTHT14Labs, wR8fR821pTHT14Nums, 2048),
    (wR8fR821pTHT15Labs, wR8fR821pTHT15Nums, 2048), (wR8fR821pTHT16Labs, wR8fR821pTHT16Nums,
    808)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wR8fR821pT_Wsh : wR8fR821pTW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR821pTGT0Labs, wR8fR821pTGT0Nums, 2048), (wR8fR821pTGT1Labs, wR8fR821pTGT1Nums, 2048),
    (wR8fR821pTGT2Labs, wR8fR821pTGT2Nums, 2048), (wR8fR821pTGT3Labs, wR8fR821pTGT3Nums, 2048),
    (wR8fR821pTGT4Labs, wR8fR821pTGT4Nums, 2048), (wR8fR821pTGT5Labs, wR8fR821pTGT5Nums, 2048),
    (wR8fR821pTGT6Labs, wR8fR821pTGT6Nums, 2048), (wR8fR821pTGT7Labs, wR8fR821pTGT7Nums, 2048),
    (wR8fR821pTGT8Labs, wR8fR821pTGT8Nums, 2048), (wR8fR821pTGT9Labs, wR8fR821pTGT9Nums, 2048),
    (wR8fR821pTGT10Labs, wR8fR821pTGT10Nums, 2048), (wR8fR821pTGT11Labs, wR8fR821pTGT11Nums,
    2048), (wR8fR821pTGT12Labs, wR8fR821pTGT12Nums, 2048), (wR8fR821pTGT13Labs,
    wR8fR821pTGT13Nums, 2048), (wR8fR821pTGT14Labs, wR8fR821pTGT14Nums, 1640)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wR8fR821pT_hok : octPackOk 64 wR8fR821pTL = true :=
  OctadDense.octPackOk_of_chk 64 6 true wR8fR821pTL _ _ 1007488 wR8fR821pT_Lsh wR8fR821pT_chk

/-- The octad integer sum. -/
theorem wR8fR821pT_octn : octSumZ 64 true wR8fR821pTL wR8fR821pTW = 1007488 :=
  OctadDense.octSumZ_of_chk 64 6 true wR8fR821pTL wR8fR821pTW _ _ 1007488 wR8fR821pT_Lsh
      wR8fR821pT_Wsh wR8fR821pT_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wR8fR821pT_selfchk : OctadDense.selfOctChk 64 [(wR8fR821pTGT0Labs, wR8fR821pTGT0Nums,
    2048), (wR8fR821pTGT1Labs, wR8fR821pTGT1Nums, 2048), (wR8fR821pTGT2Labs, wR8fR821pTGT2Nums,
    2048), (wR8fR821pTGT3Labs, wR8fR821pTGT3Nums, 2048), (wR8fR821pTGT4Labs, wR8fR821pTGT4Nums,
    2048), (wR8fR821pTGT5Labs, wR8fR821pTGT5Nums, 2048), (wR8fR821pTGT6Labs, wR8fR821pTGT6Nums,
    2048), (wR8fR821pTGT7Labs, wR8fR821pTGT7Nums, 2048), (wR8fR821pTGT8Labs, wR8fR821pTGT8Nums,
    2048), (wR8fR821pTGT9Labs, wR8fR821pTGT9Nums, 2048), (wR8fR821pTGT10Labs, wR8fR821pTGT10Nums,
    2048), (wR8fR821pTGT11Labs, wR8fR821pTGT11Nums, 2048), (wR8fR821pTGT12Labs,
    wR8fR821pTGT12Nums, 2048), (wR8fR821pTGT13Labs, wR8fR821pTGT13Nums, 2048),
    (wR8fR821pTGT14Labs, wR8fR821pTGT14Nums, 1640)] 31484 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wR8fR821pT_hn : wR8fR821pTL.sden * (octSumZ 64 true wR8fR821pTL wR8fR821pTW : ℚ) / 8 =
    wR8fR821pTW.sden * (selfOctP wR8fR821pTW : ℚ) := by
  rw [wR8fR821pT_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wR8fR821pTW _ 31484
      wR8fR821pT_Wsh wR8fR821pT_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
