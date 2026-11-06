/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN3nXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (octads) of the identification Ninth[5]- <-> Twelfth[31]+ (record gninth:N3-,
e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGninthN3nX_chk : OctadDense.octSumChk 64 6 false [(wGninthN3nXHT0Labs,
    wGninthN3nXHT0Nums, 2048), (wGninthN3nXHT1Labs, wGninthN3nXHT1Nums, 2048),
    (wGninthN3nXHT2Labs, wGninthN3nXHT2Nums, 2048), (wGninthN3nXHT3Labs, wGninthN3nXHT3Nums,
    2048), (wGninthN3nXHT4Labs, wGninthN3nXHT4Nums, 2048), (wGninthN3nXHT5Labs,
    wGninthN3nXHT5Nums, 2048), (wGninthN3nXHT6Labs, wGninthN3nXHT6Nums, 2048),
    (wGninthN3nXHT7Labs, wGninthN3nXHT7Nums, 2048), (wGninthN3nXHT8Labs, wGninthN3nXHT8Nums,
    2048), (wGninthN3nXHT9Labs, wGninthN3nXHT9Nums, 2048), (wGninthN3nXHT10Labs,
    wGninthN3nXHT10Nums, 2048), (wGninthN3nXHT11Labs, wGninthN3nXHT11Nums, 2048),
    (wGninthN3nXHT12Labs, wGninthN3nXHT12Nums, 2048), (wGninthN3nXHT13Labs, wGninthN3nXHT13Nums,
    2048), (wGninthN3nXHT14Labs, wGninthN3nXHT14Nums, 2048), (wGninthN3nXHT15Labs,
    wGninthN3nXHT15Nums, 2048), (wGninthN3nXHT16Labs, wGninthN3nXHT16Nums, 2048),
    (wGninthN3nXHT17Labs, wGninthN3nXHT17Nums, 2048), (wGninthN3nXHT18Labs, wGninthN3nXHT18Nums,
    2048), (wGninthN3nXHT19Labs, wGninthN3nXHT19Nums, 2048), (wGninthN3nXHT20Labs,
    wGninthN3nXHT20Nums, 2048), (wGninthN3nXHT21Labs, wGninthN3nXHT21Nums, 2048),
    (wGninthN3nXHT22Labs, wGninthN3nXHT22Nums, 2048), (wGninthN3nXHT23Labs, wGninthN3nXHT23Nums,
    2048), (wGninthN3nXHT24Labs, wGninthN3nXHT24Nums, 2048), (wGninthN3nXHT25Labs,
    wGninthN3nXHT25Nums, 2048), (wGninthN3nXHT26Labs, wGninthN3nXHT26Nums, 2048),
    (wGninthN3nXHT27Labs, wGninthN3nXHT27Nums, 2048), (wGninthN3nXHT28Labs, wGninthN3nXHT28Nums,
    2048), (wGninthN3nXHT29Labs, wGninthN3nXHT29Nums, 2048), (wGninthN3nXHT30Labs,
    wGninthN3nXHT30Nums, 144)] [(wGninthN3nXGT0Labs, wGninthN3nXGT0Nums, 2048),
    (wGninthN3nXGT1Labs, wGninthN3nXGT1Nums, 2048), (wGninthN3nXGT2Labs, wGninthN3nXGT2Nums,
    2048), (wGninthN3nXGT3Labs, wGninthN3nXGT3Nums, 2048), (wGninthN3nXGT4Labs,
    wGninthN3nXGT4Nums, 2048), (wGninthN3nXGT5Labs, wGninthN3nXGT5Nums, 2048),
    (wGninthN3nXGT6Labs, wGninthN3nXGT6Nums, 2048), (wGninthN3nXGT7Labs, wGninthN3nXGT7Nums,
    2048), (wGninthN3nXGT8Labs, wGninthN3nXGT8Nums, 2048), (wGninthN3nXGT9Labs,
    wGninthN3nXGT9Nums, 2048), (wGninthN3nXGT10Labs, wGninthN3nXGT10Nums, 2048),
    (wGninthN3nXGT11Labs, wGninthN3nXGT11Nums, 2048), (wGninthN3nXGT12Labs, wGninthN3nXGT12Nums,
    2048), (wGninthN3nXGT13Labs, wGninthN3nXGT13Nums, 2048), (wGninthN3nXGT14Labs,
    wGninthN3nXGT14Nums, 2048), (wGninthN3nXGT15Labs, wGninthN3nXGT15Nums, 2048),
    (wGninthN3nXGT16Labs, wGninthN3nXGT16Nums, 2048), (wGninthN3nXGT17Labs, wGninthN3nXGT17Nums,
    2048), (wGninthN3nXGT18Labs, wGninthN3nXGT18Nums, 2048), (wGninthN3nXGT19Labs,
    wGninthN3nXGT19Nums, 2048), (wGninthN3nXGT20Labs, wGninthN3nXGT20Nums, 2048),
    (wGninthN3nXGT21Labs, wGninthN3nXGT21Nums, 2048), (wGninthN3nXGT22Labs, wGninthN3nXGT22Nums,
    1704)] 4050944 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGninthN3nX_Lsh : wGninthN3nXL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN3nXHT0Labs, wGninthN3nXHT0Nums, 2048), (wGninthN3nXHT1Labs, wGninthN3nXHT1Nums,
    2048), (wGninthN3nXHT2Labs, wGninthN3nXHT2Nums, 2048), (wGninthN3nXHT3Labs,
    wGninthN3nXHT3Nums, 2048), (wGninthN3nXHT4Labs, wGninthN3nXHT4Nums, 2048),
    (wGninthN3nXHT5Labs, wGninthN3nXHT5Nums, 2048), (wGninthN3nXHT6Labs, wGninthN3nXHT6Nums,
    2048), (wGninthN3nXHT7Labs, wGninthN3nXHT7Nums, 2048), (wGninthN3nXHT8Labs,
    wGninthN3nXHT8Nums, 2048), (wGninthN3nXHT9Labs, wGninthN3nXHT9Nums, 2048),
    (wGninthN3nXHT10Labs, wGninthN3nXHT10Nums, 2048), (wGninthN3nXHT11Labs, wGninthN3nXHT11Nums,
    2048), (wGninthN3nXHT12Labs, wGninthN3nXHT12Nums, 2048), (wGninthN3nXHT13Labs,
    wGninthN3nXHT13Nums, 2048), (wGninthN3nXHT14Labs, wGninthN3nXHT14Nums, 2048),
    (wGninthN3nXHT15Labs, wGninthN3nXHT15Nums, 2048), (wGninthN3nXHT16Labs, wGninthN3nXHT16Nums,
    2048), (wGninthN3nXHT17Labs, wGninthN3nXHT17Nums, 2048), (wGninthN3nXHT18Labs,
    wGninthN3nXHT18Nums, 2048), (wGninthN3nXHT19Labs, wGninthN3nXHT19Nums, 2048),
    (wGninthN3nXHT20Labs, wGninthN3nXHT20Nums, 2048), (wGninthN3nXHT21Labs, wGninthN3nXHT21Nums,
    2048), (wGninthN3nXHT22Labs, wGninthN3nXHT22Nums, 2048), (wGninthN3nXHT23Labs,
    wGninthN3nXHT23Nums, 2048), (wGninthN3nXHT24Labs, wGninthN3nXHT24Nums, 2048),
    (wGninthN3nXHT25Labs, wGninthN3nXHT25Nums, 2048), (wGninthN3nXHT26Labs, wGninthN3nXHT26Nums,
    2048), (wGninthN3nXHT27Labs, wGninthN3nXHT27Nums, 2048), (wGninthN3nXHT28Labs,
    wGninthN3nXHT28Nums, 2048), (wGninthN3nXHT29Labs, wGninthN3nXHT29Nums, 2048),
    (wGninthN3nXHT30Labs, wGninthN3nXHT30Nums, 144)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGninthN3nX_Wsh : wGninthN3nXW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN3nXGT0Labs, wGninthN3nXGT0Nums, 2048), (wGninthN3nXGT1Labs, wGninthN3nXGT1Nums,
    2048), (wGninthN3nXGT2Labs, wGninthN3nXGT2Nums, 2048), (wGninthN3nXGT3Labs,
    wGninthN3nXGT3Nums, 2048), (wGninthN3nXGT4Labs, wGninthN3nXGT4Nums, 2048),
    (wGninthN3nXGT5Labs, wGninthN3nXGT5Nums, 2048), (wGninthN3nXGT6Labs, wGninthN3nXGT6Nums,
    2048), (wGninthN3nXGT7Labs, wGninthN3nXGT7Nums, 2048), (wGninthN3nXGT8Labs,
    wGninthN3nXGT8Nums, 2048), (wGninthN3nXGT9Labs, wGninthN3nXGT9Nums, 2048),
    (wGninthN3nXGT10Labs, wGninthN3nXGT10Nums, 2048), (wGninthN3nXGT11Labs, wGninthN3nXGT11Nums,
    2048), (wGninthN3nXGT12Labs, wGninthN3nXGT12Nums, 2048), (wGninthN3nXGT13Labs,
    wGninthN3nXGT13Nums, 2048), (wGninthN3nXGT14Labs, wGninthN3nXGT14Nums, 2048),
    (wGninthN3nXGT15Labs, wGninthN3nXGT15Nums, 2048), (wGninthN3nXGT16Labs, wGninthN3nXGT16Nums,
    2048), (wGninthN3nXGT17Labs, wGninthN3nXGT17Nums, 2048), (wGninthN3nXGT18Labs,
    wGninthN3nXGT18Nums, 2048), (wGninthN3nXGT19Labs, wGninthN3nXGT19Nums, 2048),
    (wGninthN3nXGT20Labs, wGninthN3nXGT20Nums, 2048), (wGninthN3nXGT21Labs, wGninthN3nXGT21Nums,
    2048), (wGninthN3nXGT22Labs, wGninthN3nXGT22Nums, 1704)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGninthN3nX_hok : octPackOk 64 wGninthN3nXL = true :=
  OctadDense.octPackOk_of_chk 64 6 false wGninthN3nXL _ _ 4050944 wGninthN3nX_Lsh wGninthN3nX_chk

/-- The octad integer sum. -/
theorem wGninthN3nX_octn : octSumZ 64 false wGninthN3nXL wGninthN3nXW = 4050944 :=
  OctadDense.octSumZ_of_chk 64 6 false wGninthN3nXL wGninthN3nXW _ _ 4050944 wGninthN3nX_Lsh
      wGninthN3nX_Wsh wGninthN3nX_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGninthN3nX_selfchk : OctadDense.selfOctChk 64 [(wGninthN3nXGT0Labs, wGninthN3nXGT0Nums,
    2048), (wGninthN3nXGT1Labs, wGninthN3nXGT1Nums, 2048), (wGninthN3nXGT2Labs,
    wGninthN3nXGT2Nums, 2048), (wGninthN3nXGT3Labs, wGninthN3nXGT3Nums, 2048),
    (wGninthN3nXGT4Labs, wGninthN3nXGT4Nums, 2048), (wGninthN3nXGT5Labs, wGninthN3nXGT5Nums,
    2048), (wGninthN3nXGT6Labs, wGninthN3nXGT6Nums, 2048), (wGninthN3nXGT7Labs,
    wGninthN3nXGT7Nums, 2048), (wGninthN3nXGT8Labs, wGninthN3nXGT8Nums, 2048),
    (wGninthN3nXGT9Labs, wGninthN3nXGT9Nums, 2048), (wGninthN3nXGT10Labs, wGninthN3nXGT10Nums,
    2048), (wGninthN3nXGT11Labs, wGninthN3nXGT11Nums, 2048), (wGninthN3nXGT12Labs,
    wGninthN3nXGT12Nums, 2048), (wGninthN3nXGT13Labs, wGninthN3nXGT13Nums, 2048),
    (wGninthN3nXGT14Labs, wGninthN3nXGT14Nums, 2048), (wGninthN3nXGT15Labs, wGninthN3nXGT15Nums,
    2048), (wGninthN3nXGT16Labs, wGninthN3nXGT16Nums, 2048), (wGninthN3nXGT17Labs,
    wGninthN3nXGT17Nums, 2048), (wGninthN3nXGT18Labs, wGninthN3nXGT18Nums, 2048),
    (wGninthN3nXGT19Labs, wGninthN3nXGT19Nums, 2048), (wGninthN3nXGT20Labs, wGninthN3nXGT20Nums,
    2048), (wGninthN3nXGT21Labs, wGninthN3nXGT21Nums, 2048), (wGninthN3nXGT22Labs,
    wGninthN3nXGT22Nums, 1704)] 506368 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGninthN3nX_hn : wGninthN3nXL.sden * (octSumZ 64 false wGninthN3nXL wGninthN3nXW : ℚ) / 8 =
    wGninthN3nXW.sden * (selfOctP wGninthN3nXW : ℚ) := by
  rw [wGninthN3nX_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGninthN3nXW _ 506368
      wGninthN3nX_Wsh wGninthN3nX_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
