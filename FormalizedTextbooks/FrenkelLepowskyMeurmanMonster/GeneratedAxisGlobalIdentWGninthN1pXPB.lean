/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN1pXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (octads) of the identification Ninth[1]+ <-> Twelfth[25]- (record gninth:N1+,
e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGninthN1pX_chk : OctadDense.octSumChk 64 6 true [(wGninthN1pXHT0Labs, wGninthN1pXHT0Nums,
    2048), (wGninthN1pXHT1Labs, wGninthN1pXHT1Nums, 2048), (wGninthN1pXHT2Labs,
    wGninthN1pXHT2Nums, 2048), (wGninthN1pXHT3Labs, wGninthN1pXHT3Nums, 2048),
    (wGninthN1pXHT4Labs, wGninthN1pXHT4Nums, 2048), (wGninthN1pXHT5Labs, wGninthN1pXHT5Nums,
    2048), (wGninthN1pXHT6Labs, wGninthN1pXHT6Nums, 2048), (wGninthN1pXHT7Labs,
    wGninthN1pXHT7Nums, 2048), (wGninthN1pXHT8Labs, wGninthN1pXHT8Nums, 2048),
    (wGninthN1pXHT9Labs, wGninthN1pXHT9Nums, 2048), (wGninthN1pXHT10Labs, wGninthN1pXHT10Nums,
    2048), (wGninthN1pXHT11Labs, wGninthN1pXHT11Nums, 2048), (wGninthN1pXHT12Labs,
    wGninthN1pXHT12Nums, 2048), (wGninthN1pXHT13Labs, wGninthN1pXHT13Nums, 2048),
    (wGninthN1pXHT14Labs, wGninthN1pXHT14Nums, 2048), (wGninthN1pXHT15Labs, wGninthN1pXHT15Nums,
    2048), (wGninthN1pXHT16Labs, wGninthN1pXHT16Nums, 2048), (wGninthN1pXHT17Labs,
    wGninthN1pXHT17Nums, 2048), (wGninthN1pXHT18Labs, wGninthN1pXHT18Nums, 2048),
    (wGninthN1pXHT19Labs, wGninthN1pXHT19Nums, 2048), (wGninthN1pXHT20Labs, wGninthN1pXHT20Nums,
    2048), (wGninthN1pXHT21Labs, wGninthN1pXHT21Nums, 2048), (wGninthN1pXHT22Labs,
    wGninthN1pXHT22Nums, 2048), (wGninthN1pXHT23Labs, wGninthN1pXHT23Nums, 2048),
    (wGninthN1pXHT24Labs, wGninthN1pXHT24Nums, 2048), (wGninthN1pXHT25Labs, wGninthN1pXHT25Nums,
    2048), (wGninthN1pXHT26Labs, wGninthN1pXHT26Nums, 2048), (wGninthN1pXHT27Labs,
    wGninthN1pXHT27Nums, 2048), (wGninthN1pXHT28Labs, wGninthN1pXHT28Nums, 2048),
    (wGninthN1pXHT29Labs, wGninthN1pXHT29Nums, 2048), (wGninthN1pXHT30Labs, wGninthN1pXHT30Nums,
    144)] [(wGninthN1pXGT0Labs, wGninthN1pXGT0Nums, 2048), (wGninthN1pXGT1Labs,
    wGninthN1pXGT1Nums, 2048), (wGninthN1pXGT2Labs, wGninthN1pXGT2Nums, 2048),
    (wGninthN1pXGT3Labs, wGninthN1pXGT3Nums, 2048), (wGninthN1pXGT4Labs, wGninthN1pXGT4Nums,
    2048), (wGninthN1pXGT5Labs, wGninthN1pXGT5Nums, 2048), (wGninthN1pXGT6Labs,
    wGninthN1pXGT6Nums, 2048), (wGninthN1pXGT7Labs, wGninthN1pXGT7Nums, 2048),
    (wGninthN1pXGT8Labs, wGninthN1pXGT8Nums, 2048), (wGninthN1pXGT9Labs, wGninthN1pXGT9Nums,
    2048), (wGninthN1pXGT10Labs, wGninthN1pXGT10Nums, 2048), (wGninthN1pXGT11Labs,
    wGninthN1pXGT11Nums, 2048), (wGninthN1pXGT12Labs, wGninthN1pXGT12Nums, 2048),
    (wGninthN1pXGT13Labs, wGninthN1pXGT13Nums, 2048), (wGninthN1pXGT14Labs, wGninthN1pXGT14Nums,
    2048), (wGninthN1pXGT15Labs, wGninthN1pXGT15Nums, 2048), (wGninthN1pXGT16Labs,
    wGninthN1pXGT16Nums, 2048), (wGninthN1pXGT17Labs, wGninthN1pXGT17Nums, 2048),
    (wGninthN1pXGT18Labs, wGninthN1pXGT18Nums, 2048), (wGninthN1pXGT19Labs, wGninthN1pXGT19Nums,
    2048), (wGninthN1pXGT20Labs, wGninthN1pXGT20Nums, 2048), (wGninthN1pXGT21Labs,
    wGninthN1pXGT21Nums, 2048), (wGninthN1pXGT22Labs, wGninthN1pXGT22Nums, 1704)] 4034048 = true
    := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGninthN1pX_Lsh : wGninthN1pXL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN1pXHT0Labs, wGninthN1pXHT0Nums, 2048), (wGninthN1pXHT1Labs, wGninthN1pXHT1Nums,
    2048), (wGninthN1pXHT2Labs, wGninthN1pXHT2Nums, 2048), (wGninthN1pXHT3Labs,
    wGninthN1pXHT3Nums, 2048), (wGninthN1pXHT4Labs, wGninthN1pXHT4Nums, 2048),
    (wGninthN1pXHT5Labs, wGninthN1pXHT5Nums, 2048), (wGninthN1pXHT6Labs, wGninthN1pXHT6Nums,
    2048), (wGninthN1pXHT7Labs, wGninthN1pXHT7Nums, 2048), (wGninthN1pXHT8Labs,
    wGninthN1pXHT8Nums, 2048), (wGninthN1pXHT9Labs, wGninthN1pXHT9Nums, 2048),
    (wGninthN1pXHT10Labs, wGninthN1pXHT10Nums, 2048), (wGninthN1pXHT11Labs, wGninthN1pXHT11Nums,
    2048), (wGninthN1pXHT12Labs, wGninthN1pXHT12Nums, 2048), (wGninthN1pXHT13Labs,
    wGninthN1pXHT13Nums, 2048), (wGninthN1pXHT14Labs, wGninthN1pXHT14Nums, 2048),
    (wGninthN1pXHT15Labs, wGninthN1pXHT15Nums, 2048), (wGninthN1pXHT16Labs, wGninthN1pXHT16Nums,
    2048), (wGninthN1pXHT17Labs, wGninthN1pXHT17Nums, 2048), (wGninthN1pXHT18Labs,
    wGninthN1pXHT18Nums, 2048), (wGninthN1pXHT19Labs, wGninthN1pXHT19Nums, 2048),
    (wGninthN1pXHT20Labs, wGninthN1pXHT20Nums, 2048), (wGninthN1pXHT21Labs, wGninthN1pXHT21Nums,
    2048), (wGninthN1pXHT22Labs, wGninthN1pXHT22Nums, 2048), (wGninthN1pXHT23Labs,
    wGninthN1pXHT23Nums, 2048), (wGninthN1pXHT24Labs, wGninthN1pXHT24Nums, 2048),
    (wGninthN1pXHT25Labs, wGninthN1pXHT25Nums, 2048), (wGninthN1pXHT26Labs, wGninthN1pXHT26Nums,
    2048), (wGninthN1pXHT27Labs, wGninthN1pXHT27Nums, 2048), (wGninthN1pXHT28Labs,
    wGninthN1pXHT28Nums, 2048), (wGninthN1pXHT29Labs, wGninthN1pXHT29Nums, 2048),
    (wGninthN1pXHT30Labs, wGninthN1pXHT30Nums, 144)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGninthN1pX_Wsh : wGninthN1pXW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN1pXGT0Labs, wGninthN1pXGT0Nums, 2048), (wGninthN1pXGT1Labs, wGninthN1pXGT1Nums,
    2048), (wGninthN1pXGT2Labs, wGninthN1pXGT2Nums, 2048), (wGninthN1pXGT3Labs,
    wGninthN1pXGT3Nums, 2048), (wGninthN1pXGT4Labs, wGninthN1pXGT4Nums, 2048),
    (wGninthN1pXGT5Labs, wGninthN1pXGT5Nums, 2048), (wGninthN1pXGT6Labs, wGninthN1pXGT6Nums,
    2048), (wGninthN1pXGT7Labs, wGninthN1pXGT7Nums, 2048), (wGninthN1pXGT8Labs,
    wGninthN1pXGT8Nums, 2048), (wGninthN1pXGT9Labs, wGninthN1pXGT9Nums, 2048),
    (wGninthN1pXGT10Labs, wGninthN1pXGT10Nums, 2048), (wGninthN1pXGT11Labs, wGninthN1pXGT11Nums,
    2048), (wGninthN1pXGT12Labs, wGninthN1pXGT12Nums, 2048), (wGninthN1pXGT13Labs,
    wGninthN1pXGT13Nums, 2048), (wGninthN1pXGT14Labs, wGninthN1pXGT14Nums, 2048),
    (wGninthN1pXGT15Labs, wGninthN1pXGT15Nums, 2048), (wGninthN1pXGT16Labs, wGninthN1pXGT16Nums,
    2048), (wGninthN1pXGT17Labs, wGninthN1pXGT17Nums, 2048), (wGninthN1pXGT18Labs,
    wGninthN1pXGT18Nums, 2048), (wGninthN1pXGT19Labs, wGninthN1pXGT19Nums, 2048),
    (wGninthN1pXGT20Labs, wGninthN1pXGT20Nums, 2048), (wGninthN1pXGT21Labs, wGninthN1pXGT21Nums,
    2048), (wGninthN1pXGT22Labs, wGninthN1pXGT22Nums, 1704)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGninthN1pX_hok : octPackOk 64 wGninthN1pXL = true :=
  OctadDense.octPackOk_of_chk 64 6 true wGninthN1pXL _ _ 4034048 wGninthN1pX_Lsh wGninthN1pX_chk

/-- The octad integer sum. -/
theorem wGninthN1pX_octn : octSumZ 64 true wGninthN1pXL wGninthN1pXW = 4034048 :=
  OctadDense.octSumZ_of_chk 64 6 true wGninthN1pXL wGninthN1pXW _ _ 4034048 wGninthN1pX_Lsh
      wGninthN1pX_Wsh wGninthN1pX_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGninthN1pX_selfchk : OctadDense.selfOctChk 64 [(wGninthN1pXGT0Labs, wGninthN1pXGT0Nums,
    2048), (wGninthN1pXGT1Labs, wGninthN1pXGT1Nums, 2048), (wGninthN1pXGT2Labs,
    wGninthN1pXGT2Nums, 2048), (wGninthN1pXGT3Labs, wGninthN1pXGT3Nums, 2048),
    (wGninthN1pXGT4Labs, wGninthN1pXGT4Nums, 2048), (wGninthN1pXGT5Labs, wGninthN1pXGT5Nums,
    2048), (wGninthN1pXGT6Labs, wGninthN1pXGT6Nums, 2048), (wGninthN1pXGT7Labs,
    wGninthN1pXGT7Nums, 2048), (wGninthN1pXGT8Labs, wGninthN1pXGT8Nums, 2048),
    (wGninthN1pXGT9Labs, wGninthN1pXGT9Nums, 2048), (wGninthN1pXGT10Labs, wGninthN1pXGT10Nums,
    2048), (wGninthN1pXGT11Labs, wGninthN1pXGT11Nums, 2048), (wGninthN1pXGT12Labs,
    wGninthN1pXGT12Nums, 2048), (wGninthN1pXGT13Labs, wGninthN1pXGT13Nums, 2048),
    (wGninthN1pXGT14Labs, wGninthN1pXGT14Nums, 2048), (wGninthN1pXGT15Labs, wGninthN1pXGT15Nums,
    2048), (wGninthN1pXGT16Labs, wGninthN1pXGT16Nums, 2048), (wGninthN1pXGT17Labs,
    wGninthN1pXGT17Nums, 2048), (wGninthN1pXGT18Labs, wGninthN1pXGT18Nums, 2048),
    (wGninthN1pXGT19Labs, wGninthN1pXGT19Nums, 2048), (wGninthN1pXGT20Labs, wGninthN1pXGT20Nums,
    2048), (wGninthN1pXGT21Labs, wGninthN1pXGT21Nums, 2048), (wGninthN1pXGT22Labs,
    wGninthN1pXGT22Nums, 1704)] 504256 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGninthN1pX_hn : wGninthN1pXL.sden * (octSumZ 64 true wGninthN1pXL wGninthN1pXW : ℚ) / 8 =
    wGninthN1pXW.sden * (selfOctP wGninthN1pXW : ℚ) := by
  rw [wGninthN1pX_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGninthN1pXW _ 504256
      wGninthN1pX_Wsh wGninthN1pX_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
