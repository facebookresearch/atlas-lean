/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN3pXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (octads) of the identification Ninth[5]+ <-> Twelfth[31]+ (record gninth:N3+,
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
theorem wGninthN3pX_chk : OctadDense.octSumChk 64 6 true [(wGninthN3pXHT0Labs, wGninthN3pXHT0Nums,
    2048), (wGninthN3pXHT1Labs, wGninthN3pXHT1Nums, 2048), (wGninthN3pXHT2Labs,
    wGninthN3pXHT2Nums, 2048), (wGninthN3pXHT3Labs, wGninthN3pXHT3Nums, 2048),
    (wGninthN3pXHT4Labs, wGninthN3pXHT4Nums, 2048), (wGninthN3pXHT5Labs, wGninthN3pXHT5Nums,
    2048), (wGninthN3pXHT6Labs, wGninthN3pXHT6Nums, 2048), (wGninthN3pXHT7Labs,
    wGninthN3pXHT7Nums, 2048), (wGninthN3pXHT8Labs, wGninthN3pXHT8Nums, 2048),
    (wGninthN3pXHT9Labs, wGninthN3pXHT9Nums, 2048), (wGninthN3pXHT10Labs, wGninthN3pXHT10Nums,
    2048), (wGninthN3pXHT11Labs, wGninthN3pXHT11Nums, 2048), (wGninthN3pXHT12Labs,
    wGninthN3pXHT12Nums, 2048), (wGninthN3pXHT13Labs, wGninthN3pXHT13Nums, 2048),
    (wGninthN3pXHT14Labs, wGninthN3pXHT14Nums, 2048), (wGninthN3pXHT15Labs, wGninthN3pXHT15Nums,
    2048), (wGninthN3pXHT16Labs, wGninthN3pXHT16Nums, 2048), (wGninthN3pXHT17Labs,
    wGninthN3pXHT17Nums, 2048), (wGninthN3pXHT18Labs, wGninthN3pXHT18Nums, 2048),
    (wGninthN3pXHT19Labs, wGninthN3pXHT19Nums, 2048), (wGninthN3pXHT20Labs, wGninthN3pXHT20Nums,
    2048), (wGninthN3pXHT21Labs, wGninthN3pXHT21Nums, 2048), (wGninthN3pXHT22Labs,
    wGninthN3pXHT22Nums, 2048), (wGninthN3pXHT23Labs, wGninthN3pXHT23Nums, 2048),
    (wGninthN3pXHT24Labs, wGninthN3pXHT24Nums, 2048), (wGninthN3pXHT25Labs, wGninthN3pXHT25Nums,
    2048), (wGninthN3pXHT26Labs, wGninthN3pXHT26Nums, 2048), (wGninthN3pXHT27Labs,
    wGninthN3pXHT27Nums, 2048), (wGninthN3pXHT28Labs, wGninthN3pXHT28Nums, 2048),
    (wGninthN3pXHT29Labs, wGninthN3pXHT29Nums, 2048), (wGninthN3pXHT30Labs, wGninthN3pXHT30Nums,
    144)] [(wGninthN3pXGT0Labs, wGninthN3pXGT0Nums, 2048), (wGninthN3pXGT1Labs,
    wGninthN3pXGT1Nums, 2048), (wGninthN3pXGT2Labs, wGninthN3pXGT2Nums, 2048),
    (wGninthN3pXGT3Labs, wGninthN3pXGT3Nums, 2048), (wGninthN3pXGT4Labs, wGninthN3pXGT4Nums,
    2048), (wGninthN3pXGT5Labs, wGninthN3pXGT5Nums, 2048), (wGninthN3pXGT6Labs,
    wGninthN3pXGT6Nums, 2048), (wGninthN3pXGT7Labs, wGninthN3pXGT7Nums, 2048),
    (wGninthN3pXGT8Labs, wGninthN3pXGT8Nums, 2048), (wGninthN3pXGT9Labs, wGninthN3pXGT9Nums,
    2048), (wGninthN3pXGT10Labs, wGninthN3pXGT10Nums, 2048), (wGninthN3pXGT11Labs,
    wGninthN3pXGT11Nums, 2048), (wGninthN3pXGT12Labs, wGninthN3pXGT12Nums, 2048),
    (wGninthN3pXGT13Labs, wGninthN3pXGT13Nums, 2048), (wGninthN3pXGT14Labs, wGninthN3pXGT14Nums,
    2048), (wGninthN3pXGT15Labs, wGninthN3pXGT15Nums, 2048), (wGninthN3pXGT16Labs,
    wGninthN3pXGT16Nums, 2048), (wGninthN3pXGT17Labs, wGninthN3pXGT17Nums, 2048),
    (wGninthN3pXGT18Labs, wGninthN3pXGT18Nums, 2048), (wGninthN3pXGT19Labs, wGninthN3pXGT19Nums,
    2048), (wGninthN3pXGT20Labs, wGninthN3pXGT20Nums, 2048), (wGninthN3pXGT21Labs,
    wGninthN3pXGT21Nums, 2048), (wGninthN3pXGT22Labs, wGninthN3pXGT22Nums, 1704)] 4050944 = true
    := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGninthN3pX_Lsh : wGninthN3pXL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN3pXHT0Labs, wGninthN3pXHT0Nums, 2048), (wGninthN3pXHT1Labs, wGninthN3pXHT1Nums,
    2048), (wGninthN3pXHT2Labs, wGninthN3pXHT2Nums, 2048), (wGninthN3pXHT3Labs,
    wGninthN3pXHT3Nums, 2048), (wGninthN3pXHT4Labs, wGninthN3pXHT4Nums, 2048),
    (wGninthN3pXHT5Labs, wGninthN3pXHT5Nums, 2048), (wGninthN3pXHT6Labs, wGninthN3pXHT6Nums,
    2048), (wGninthN3pXHT7Labs, wGninthN3pXHT7Nums, 2048), (wGninthN3pXHT8Labs,
    wGninthN3pXHT8Nums, 2048), (wGninthN3pXHT9Labs, wGninthN3pXHT9Nums, 2048),
    (wGninthN3pXHT10Labs, wGninthN3pXHT10Nums, 2048), (wGninthN3pXHT11Labs, wGninthN3pXHT11Nums,
    2048), (wGninthN3pXHT12Labs, wGninthN3pXHT12Nums, 2048), (wGninthN3pXHT13Labs,
    wGninthN3pXHT13Nums, 2048), (wGninthN3pXHT14Labs, wGninthN3pXHT14Nums, 2048),
    (wGninthN3pXHT15Labs, wGninthN3pXHT15Nums, 2048), (wGninthN3pXHT16Labs, wGninthN3pXHT16Nums,
    2048), (wGninthN3pXHT17Labs, wGninthN3pXHT17Nums, 2048), (wGninthN3pXHT18Labs,
    wGninthN3pXHT18Nums, 2048), (wGninthN3pXHT19Labs, wGninthN3pXHT19Nums, 2048),
    (wGninthN3pXHT20Labs, wGninthN3pXHT20Nums, 2048), (wGninthN3pXHT21Labs, wGninthN3pXHT21Nums,
    2048), (wGninthN3pXHT22Labs, wGninthN3pXHT22Nums, 2048), (wGninthN3pXHT23Labs,
    wGninthN3pXHT23Nums, 2048), (wGninthN3pXHT24Labs, wGninthN3pXHT24Nums, 2048),
    (wGninthN3pXHT25Labs, wGninthN3pXHT25Nums, 2048), (wGninthN3pXHT26Labs, wGninthN3pXHT26Nums,
    2048), (wGninthN3pXHT27Labs, wGninthN3pXHT27Nums, 2048), (wGninthN3pXHT28Labs,
    wGninthN3pXHT28Nums, 2048), (wGninthN3pXHT29Labs, wGninthN3pXHT29Nums, 2048),
    (wGninthN3pXHT30Labs, wGninthN3pXHT30Nums, 144)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGninthN3pX_Wsh : wGninthN3pXW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN3pXGT0Labs, wGninthN3pXGT0Nums, 2048), (wGninthN3pXGT1Labs, wGninthN3pXGT1Nums,
    2048), (wGninthN3pXGT2Labs, wGninthN3pXGT2Nums, 2048), (wGninthN3pXGT3Labs,
    wGninthN3pXGT3Nums, 2048), (wGninthN3pXGT4Labs, wGninthN3pXGT4Nums, 2048),
    (wGninthN3pXGT5Labs, wGninthN3pXGT5Nums, 2048), (wGninthN3pXGT6Labs, wGninthN3pXGT6Nums,
    2048), (wGninthN3pXGT7Labs, wGninthN3pXGT7Nums, 2048), (wGninthN3pXGT8Labs,
    wGninthN3pXGT8Nums, 2048), (wGninthN3pXGT9Labs, wGninthN3pXGT9Nums, 2048),
    (wGninthN3pXGT10Labs, wGninthN3pXGT10Nums, 2048), (wGninthN3pXGT11Labs, wGninthN3pXGT11Nums,
    2048), (wGninthN3pXGT12Labs, wGninthN3pXGT12Nums, 2048), (wGninthN3pXGT13Labs,
    wGninthN3pXGT13Nums, 2048), (wGninthN3pXGT14Labs, wGninthN3pXGT14Nums, 2048),
    (wGninthN3pXGT15Labs, wGninthN3pXGT15Nums, 2048), (wGninthN3pXGT16Labs, wGninthN3pXGT16Nums,
    2048), (wGninthN3pXGT17Labs, wGninthN3pXGT17Nums, 2048), (wGninthN3pXGT18Labs,
    wGninthN3pXGT18Nums, 2048), (wGninthN3pXGT19Labs, wGninthN3pXGT19Nums, 2048),
    (wGninthN3pXGT20Labs, wGninthN3pXGT20Nums, 2048), (wGninthN3pXGT21Labs, wGninthN3pXGT21Nums,
    2048), (wGninthN3pXGT22Labs, wGninthN3pXGT22Nums, 1704)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGninthN3pX_hok : octPackOk 64 wGninthN3pXL = true :=
  OctadDense.octPackOk_of_chk 64 6 true wGninthN3pXL _ _ 4050944 wGninthN3pX_Lsh wGninthN3pX_chk

/-- The octad integer sum. -/
theorem wGninthN3pX_octn : octSumZ 64 true wGninthN3pXL wGninthN3pXW = 4050944 :=
  OctadDense.octSumZ_of_chk 64 6 true wGninthN3pXL wGninthN3pXW _ _ 4050944 wGninthN3pX_Lsh
      wGninthN3pX_Wsh wGninthN3pX_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGninthN3pX_selfchk : OctadDense.selfOctChk 64 [(wGninthN3pXGT0Labs, wGninthN3pXGT0Nums,
    2048), (wGninthN3pXGT1Labs, wGninthN3pXGT1Nums, 2048), (wGninthN3pXGT2Labs,
    wGninthN3pXGT2Nums, 2048), (wGninthN3pXGT3Labs, wGninthN3pXGT3Nums, 2048),
    (wGninthN3pXGT4Labs, wGninthN3pXGT4Nums, 2048), (wGninthN3pXGT5Labs, wGninthN3pXGT5Nums,
    2048), (wGninthN3pXGT6Labs, wGninthN3pXGT6Nums, 2048), (wGninthN3pXGT7Labs,
    wGninthN3pXGT7Nums, 2048), (wGninthN3pXGT8Labs, wGninthN3pXGT8Nums, 2048),
    (wGninthN3pXGT9Labs, wGninthN3pXGT9Nums, 2048), (wGninthN3pXGT10Labs, wGninthN3pXGT10Nums,
    2048), (wGninthN3pXGT11Labs, wGninthN3pXGT11Nums, 2048), (wGninthN3pXGT12Labs,
    wGninthN3pXGT12Nums, 2048), (wGninthN3pXGT13Labs, wGninthN3pXGT13Nums, 2048),
    (wGninthN3pXGT14Labs, wGninthN3pXGT14Nums, 2048), (wGninthN3pXGT15Labs, wGninthN3pXGT15Nums,
    2048), (wGninthN3pXGT16Labs, wGninthN3pXGT16Nums, 2048), (wGninthN3pXGT17Labs,
    wGninthN3pXGT17Nums, 2048), (wGninthN3pXGT18Labs, wGninthN3pXGT18Nums, 2048),
    (wGninthN3pXGT19Labs, wGninthN3pXGT19Nums, 2048), (wGninthN3pXGT20Labs, wGninthN3pXGT20Nums,
    2048), (wGninthN3pXGT21Labs, wGninthN3pXGT21Nums, 2048), (wGninthN3pXGT22Labs,
    wGninthN3pXGT22Nums, 1704)] 506368 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGninthN3pX_hn : wGninthN3pXL.sden * (octSumZ 64 true wGninthN3pXL wGninthN3pXW : ℚ) / 8 =
    wGninthN3pXW.sden * (selfOctP wGninthN3pXW : ℚ) := by
  rw [wGninthN3pX_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGninthN3pXW _ 506368
      wGninthN3pX_Wsh wGninthN3pX_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
