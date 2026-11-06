/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR822pTChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixthF

/-! # Factory parts (octads) of the identification Root8[4]+ <-> Sixth[14]+ (record r8f:R822+, e =
1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wR8fR822pT_chk : OctadDense.octSumChk 64 6 true [(wR8fR822pTHT0Labs, wR8fR822pTHT0Nums,
    2048), (wR8fR822pTHT1Labs, wR8fR822pTHT1Nums, 2048), (wR8fR822pTHT2Labs, wR8fR822pTHT2Nums,
    2048), (wR8fR822pTHT3Labs, wR8fR822pTHT3Nums, 2048), (wR8fR822pTHT4Labs, wR8fR822pTHT4Nums,
    2048), (wR8fR822pTHT5Labs, wR8fR822pTHT5Nums, 2048), (wR8fR822pTHT6Labs, wR8fR822pTHT6Nums,
    2048), (wR8fR822pTHT7Labs, wR8fR822pTHT7Nums, 2048), (wR8fR822pTHT8Labs, wR8fR822pTHT8Nums,
    2048), (wR8fR822pTHT9Labs, wR8fR822pTHT9Nums, 2048), (wR8fR822pTHT10Labs, wR8fR822pTHT10Nums,
    2048), (wR8fR822pTHT11Labs, wR8fR822pTHT11Nums, 2048), (wR8fR822pTHT12Labs,
    wR8fR822pTHT12Nums, 2048), (wR8fR822pTHT13Labs, wR8fR822pTHT13Nums, 2048),
    (wR8fR822pTHT14Labs, wR8fR822pTHT14Nums, 2048), (wR8fR822pTHT15Labs, wR8fR822pTHT15Nums,
    2048), (wR8fR822pTHT16Labs, wR8fR822pTHT16Nums, 808)] [(wR8fR822pTGT0Labs, wR8fR822pTGT0Nums,
    2048), (wR8fR822pTGT1Labs, wR8fR822pTGT1Nums, 2048), (wR8fR822pTGT2Labs, wR8fR822pTGT2Nums,
    2048), (wR8fR822pTGT3Labs, wR8fR822pTGT3Nums, 2048), (wR8fR822pTGT4Labs, wR8fR822pTGT4Nums,
    2048), (wR8fR822pTGT5Labs, wR8fR822pTGT5Nums, 2048), (wR8fR822pTGT6Labs, wR8fR822pTGT6Nums,
    2048), (wR8fR822pTGT7Labs, wR8fR822pTGT7Nums, 2048), (wR8fR822pTGT8Labs, wR8fR822pTGT8Nums,
    2048), (wR8fR822pTGT9Labs, wR8fR822pTGT9Nums, 2048), (wR8fR822pTGT10Labs, wR8fR822pTGT10Nums,
    2048), (wR8fR822pTGT11Labs, wR8fR822pTGT11Nums, 2048), (wR8fR822pTGT12Labs,
    wR8fR822pTGT12Nums, 2048), (wR8fR822pTGT13Labs, wR8fR822pTGT13Nums, 2048),
    (wR8fR822pTGT14Labs, wR8fR822pTGT14Nums, 1640)] 998272 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wR8fR822pT_Lsh : wR8fR822pTL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR822pTHT0Labs, wR8fR822pTHT0Nums, 2048), (wR8fR822pTHT1Labs, wR8fR822pTHT1Nums, 2048),
    (wR8fR822pTHT2Labs, wR8fR822pTHT2Nums, 2048), (wR8fR822pTHT3Labs, wR8fR822pTHT3Nums, 2048),
    (wR8fR822pTHT4Labs, wR8fR822pTHT4Nums, 2048), (wR8fR822pTHT5Labs, wR8fR822pTHT5Nums, 2048),
    (wR8fR822pTHT6Labs, wR8fR822pTHT6Nums, 2048), (wR8fR822pTHT7Labs, wR8fR822pTHT7Nums, 2048),
    (wR8fR822pTHT8Labs, wR8fR822pTHT8Nums, 2048), (wR8fR822pTHT9Labs, wR8fR822pTHT9Nums, 2048),
    (wR8fR822pTHT10Labs, wR8fR822pTHT10Nums, 2048), (wR8fR822pTHT11Labs, wR8fR822pTHT11Nums,
    2048), (wR8fR822pTHT12Labs, wR8fR822pTHT12Nums, 2048), (wR8fR822pTHT13Labs,
    wR8fR822pTHT13Nums, 2048), (wR8fR822pTHT14Labs, wR8fR822pTHT14Nums, 2048),
    (wR8fR822pTHT15Labs, wR8fR822pTHT15Nums, 2048), (wR8fR822pTHT16Labs, wR8fR822pTHT16Nums,
    808)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wR8fR822pT_Wsh : wR8fR822pTW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR822pTGT0Labs, wR8fR822pTGT0Nums, 2048), (wR8fR822pTGT1Labs, wR8fR822pTGT1Nums, 2048),
    (wR8fR822pTGT2Labs, wR8fR822pTGT2Nums, 2048), (wR8fR822pTGT3Labs, wR8fR822pTGT3Nums, 2048),
    (wR8fR822pTGT4Labs, wR8fR822pTGT4Nums, 2048), (wR8fR822pTGT5Labs, wR8fR822pTGT5Nums, 2048),
    (wR8fR822pTGT6Labs, wR8fR822pTGT6Nums, 2048), (wR8fR822pTGT7Labs, wR8fR822pTGT7Nums, 2048),
    (wR8fR822pTGT8Labs, wR8fR822pTGT8Nums, 2048), (wR8fR822pTGT9Labs, wR8fR822pTGT9Nums, 2048),
    (wR8fR822pTGT10Labs, wR8fR822pTGT10Nums, 2048), (wR8fR822pTGT11Labs, wR8fR822pTGT11Nums,
    2048), (wR8fR822pTGT12Labs, wR8fR822pTGT12Nums, 2048), (wR8fR822pTGT13Labs,
    wR8fR822pTGT13Nums, 2048), (wR8fR822pTGT14Labs, wR8fR822pTGT14Nums, 1640)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wR8fR822pT_hok : octPackOk 64 wR8fR822pTL = true :=
  OctadDense.octPackOk_of_chk 64 6 true wR8fR822pTL _ _ 998272 wR8fR822pT_Lsh wR8fR822pT_chk

/-- The octad integer sum. -/
theorem wR8fR822pT_octn : octSumZ 64 true wR8fR822pTL wR8fR822pTW = 998272 :=
  OctadDense.octSumZ_of_chk 64 6 true wR8fR822pTL wR8fR822pTW _ _ 998272 wR8fR822pT_Lsh
      wR8fR822pT_Wsh wR8fR822pT_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wR8fR822pT_selfchk : OctadDense.selfOctChk 64 [(wR8fR822pTGT0Labs, wR8fR822pTGT0Nums,
    2048), (wR8fR822pTGT1Labs, wR8fR822pTGT1Nums, 2048), (wR8fR822pTGT2Labs, wR8fR822pTGT2Nums,
    2048), (wR8fR822pTGT3Labs, wR8fR822pTGT3Nums, 2048), (wR8fR822pTGT4Labs, wR8fR822pTGT4Nums,
    2048), (wR8fR822pTGT5Labs, wR8fR822pTGT5Nums, 2048), (wR8fR822pTGT6Labs, wR8fR822pTGT6Nums,
    2048), (wR8fR822pTGT7Labs, wR8fR822pTGT7Nums, 2048), (wR8fR822pTGT8Labs, wR8fR822pTGT8Nums,
    2048), (wR8fR822pTGT9Labs, wR8fR822pTGT9Nums, 2048), (wR8fR822pTGT10Labs, wR8fR822pTGT10Nums,
    2048), (wR8fR822pTGT11Labs, wR8fR822pTGT11Nums, 2048), (wR8fR822pTGT12Labs,
    wR8fR822pTGT12Nums, 2048), (wR8fR822pTGT13Labs, wR8fR822pTGT13Nums, 2048),
    (wR8fR822pTGT14Labs, wR8fR822pTGT14Nums, 1640)] 31196 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wR8fR822pT_hn : wR8fR822pTL.sden * (octSumZ 64 true wR8fR822pTL wR8fR822pTW : ℚ) / 8 =
    wR8fR822pTW.sden * (selfOctP wR8fR822pTW : ℚ) := by
  rw [wR8fR822pT_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wR8fR822pTW _ 31196
      wR8fR822pT_Wsh wR8fR822pT_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
