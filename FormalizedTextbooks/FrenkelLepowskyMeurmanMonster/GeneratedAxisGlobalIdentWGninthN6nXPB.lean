/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN6nXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (octads) of the identification Ninth[10]- <-> Twelfth[12]- (record gninth:N6-,
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
theorem wGninthN6nX_chk : OctadDense.octSumChk 64 6 false [(wGninthN6nXHT0Labs,
    wGninthN6nXHT0Nums, 2048), (wGninthN6nXHT1Labs, wGninthN6nXHT1Nums, 2048),
    (wGninthN6nXHT2Labs, wGninthN6nXHT2Nums, 2048), (wGninthN6nXHT3Labs, wGninthN6nXHT3Nums,
    2048), (wGninthN6nXHT4Labs, wGninthN6nXHT4Nums, 2048), (wGninthN6nXHT5Labs,
    wGninthN6nXHT5Nums, 2048), (wGninthN6nXHT6Labs, wGninthN6nXHT6Nums, 2048),
    (wGninthN6nXHT7Labs, wGninthN6nXHT7Nums, 2048), (wGninthN6nXHT8Labs, wGninthN6nXHT8Nums,
    2048), (wGninthN6nXHT9Labs, wGninthN6nXHT9Nums, 2048), (wGninthN6nXHT10Labs,
    wGninthN6nXHT10Nums, 2048), (wGninthN6nXHT11Labs, wGninthN6nXHT11Nums, 2048),
    (wGninthN6nXHT12Labs, wGninthN6nXHT12Nums, 2048), (wGninthN6nXHT13Labs, wGninthN6nXHT13Nums,
    2048), (wGninthN6nXHT14Labs, wGninthN6nXHT14Nums, 2048), (wGninthN6nXHT15Labs,
    wGninthN6nXHT15Nums, 2048), (wGninthN6nXHT16Labs, wGninthN6nXHT16Nums, 2048),
    (wGninthN6nXHT17Labs, wGninthN6nXHT17Nums, 2048), (wGninthN6nXHT18Labs, wGninthN6nXHT18Nums,
    2048), (wGninthN6nXHT19Labs, wGninthN6nXHT19Nums, 2048), (wGninthN6nXHT20Labs,
    wGninthN6nXHT20Nums, 2048), (wGninthN6nXHT21Labs, wGninthN6nXHT21Nums, 2048),
    (wGninthN6nXHT22Labs, wGninthN6nXHT22Nums, 2048), (wGninthN6nXHT23Labs, wGninthN6nXHT23Nums,
    2048), (wGninthN6nXHT24Labs, wGninthN6nXHT24Nums, 2048), (wGninthN6nXHT25Labs,
    wGninthN6nXHT25Nums, 2048), (wGninthN6nXHT26Labs, wGninthN6nXHT26Nums, 2048),
    (wGninthN6nXHT27Labs, wGninthN6nXHT27Nums, 2048), (wGninthN6nXHT28Labs, wGninthN6nXHT28Nums,
    2048), (wGninthN6nXHT29Labs, wGninthN6nXHT29Nums, 2048), (wGninthN6nXHT30Labs,
    wGninthN6nXHT30Nums, 144)] [(wGninthN6nXGT0Labs, wGninthN6nXGT0Nums, 2048),
    (wGninthN6nXGT1Labs, wGninthN6nXGT1Nums, 2048), (wGninthN6nXGT2Labs, wGninthN6nXGT2Nums,
    2048), (wGninthN6nXGT3Labs, wGninthN6nXGT3Nums, 2048), (wGninthN6nXGT4Labs,
    wGninthN6nXGT4Nums, 2048), (wGninthN6nXGT5Labs, wGninthN6nXGT5Nums, 2048),
    (wGninthN6nXGT6Labs, wGninthN6nXGT6Nums, 2048), (wGninthN6nXGT7Labs, wGninthN6nXGT7Nums,
    2048), (wGninthN6nXGT8Labs, wGninthN6nXGT8Nums, 2048), (wGninthN6nXGT9Labs,
    wGninthN6nXGT9Nums, 2048), (wGninthN6nXGT10Labs, wGninthN6nXGT10Nums, 2048),
    (wGninthN6nXGT11Labs, wGninthN6nXGT11Nums, 2048), (wGninthN6nXGT12Labs, wGninthN6nXGT12Nums,
    2048), (wGninthN6nXGT13Labs, wGninthN6nXGT13Nums, 2048), (wGninthN6nXGT14Labs,
    wGninthN6nXGT14Nums, 2048), (wGninthN6nXGT15Labs, wGninthN6nXGT15Nums, 2048),
    (wGninthN6nXGT16Labs, wGninthN6nXGT16Nums, 2048), (wGninthN6nXGT17Labs, wGninthN6nXGT17Nums,
    2048), (wGninthN6nXGT18Labs, wGninthN6nXGT18Nums, 2048), (wGninthN6nXGT19Labs,
    wGninthN6nXGT19Nums, 2048), (wGninthN6nXGT20Labs, wGninthN6nXGT20Nums, 2048),
    (wGninthN6nXGT21Labs, wGninthN6nXGT21Nums, 2048), (wGninthN6nXGT22Labs, wGninthN6nXGT22Nums,
    1704)] 4055040 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGninthN6nX_Lsh : wGninthN6nXL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN6nXHT0Labs, wGninthN6nXHT0Nums, 2048), (wGninthN6nXHT1Labs, wGninthN6nXHT1Nums,
    2048), (wGninthN6nXHT2Labs, wGninthN6nXHT2Nums, 2048), (wGninthN6nXHT3Labs,
    wGninthN6nXHT3Nums, 2048), (wGninthN6nXHT4Labs, wGninthN6nXHT4Nums, 2048),
    (wGninthN6nXHT5Labs, wGninthN6nXHT5Nums, 2048), (wGninthN6nXHT6Labs, wGninthN6nXHT6Nums,
    2048), (wGninthN6nXHT7Labs, wGninthN6nXHT7Nums, 2048), (wGninthN6nXHT8Labs,
    wGninthN6nXHT8Nums, 2048), (wGninthN6nXHT9Labs, wGninthN6nXHT9Nums, 2048),
    (wGninthN6nXHT10Labs, wGninthN6nXHT10Nums, 2048), (wGninthN6nXHT11Labs, wGninthN6nXHT11Nums,
    2048), (wGninthN6nXHT12Labs, wGninthN6nXHT12Nums, 2048), (wGninthN6nXHT13Labs,
    wGninthN6nXHT13Nums, 2048), (wGninthN6nXHT14Labs, wGninthN6nXHT14Nums, 2048),
    (wGninthN6nXHT15Labs, wGninthN6nXHT15Nums, 2048), (wGninthN6nXHT16Labs, wGninthN6nXHT16Nums,
    2048), (wGninthN6nXHT17Labs, wGninthN6nXHT17Nums, 2048), (wGninthN6nXHT18Labs,
    wGninthN6nXHT18Nums, 2048), (wGninthN6nXHT19Labs, wGninthN6nXHT19Nums, 2048),
    (wGninthN6nXHT20Labs, wGninthN6nXHT20Nums, 2048), (wGninthN6nXHT21Labs, wGninthN6nXHT21Nums,
    2048), (wGninthN6nXHT22Labs, wGninthN6nXHT22Nums, 2048), (wGninthN6nXHT23Labs,
    wGninthN6nXHT23Nums, 2048), (wGninthN6nXHT24Labs, wGninthN6nXHT24Nums, 2048),
    (wGninthN6nXHT25Labs, wGninthN6nXHT25Nums, 2048), (wGninthN6nXHT26Labs, wGninthN6nXHT26Nums,
    2048), (wGninthN6nXHT27Labs, wGninthN6nXHT27Nums, 2048), (wGninthN6nXHT28Labs,
    wGninthN6nXHT28Nums, 2048), (wGninthN6nXHT29Labs, wGninthN6nXHT29Nums, 2048),
    (wGninthN6nXHT30Labs, wGninthN6nXHT30Nums, 144)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGninthN6nX_Wsh : wGninthN6nXW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN6nXGT0Labs, wGninthN6nXGT0Nums, 2048), (wGninthN6nXGT1Labs, wGninthN6nXGT1Nums,
    2048), (wGninthN6nXGT2Labs, wGninthN6nXGT2Nums, 2048), (wGninthN6nXGT3Labs,
    wGninthN6nXGT3Nums, 2048), (wGninthN6nXGT4Labs, wGninthN6nXGT4Nums, 2048),
    (wGninthN6nXGT5Labs, wGninthN6nXGT5Nums, 2048), (wGninthN6nXGT6Labs, wGninthN6nXGT6Nums,
    2048), (wGninthN6nXGT7Labs, wGninthN6nXGT7Nums, 2048), (wGninthN6nXGT8Labs,
    wGninthN6nXGT8Nums, 2048), (wGninthN6nXGT9Labs, wGninthN6nXGT9Nums, 2048),
    (wGninthN6nXGT10Labs, wGninthN6nXGT10Nums, 2048), (wGninthN6nXGT11Labs, wGninthN6nXGT11Nums,
    2048), (wGninthN6nXGT12Labs, wGninthN6nXGT12Nums, 2048), (wGninthN6nXGT13Labs,
    wGninthN6nXGT13Nums, 2048), (wGninthN6nXGT14Labs, wGninthN6nXGT14Nums, 2048),
    (wGninthN6nXGT15Labs, wGninthN6nXGT15Nums, 2048), (wGninthN6nXGT16Labs, wGninthN6nXGT16Nums,
    2048), (wGninthN6nXGT17Labs, wGninthN6nXGT17Nums, 2048), (wGninthN6nXGT18Labs,
    wGninthN6nXGT18Nums, 2048), (wGninthN6nXGT19Labs, wGninthN6nXGT19Nums, 2048),
    (wGninthN6nXGT20Labs, wGninthN6nXGT20Nums, 2048), (wGninthN6nXGT21Labs, wGninthN6nXGT21Nums,
    2048), (wGninthN6nXGT22Labs, wGninthN6nXGT22Nums, 1704)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGninthN6nX_hok : octPackOk 64 wGninthN6nXL = true :=
  OctadDense.octPackOk_of_chk 64 6 false wGninthN6nXL _ _ 4055040 wGninthN6nX_Lsh wGninthN6nX_chk

/-- The octad integer sum. -/
theorem wGninthN6nX_octn : octSumZ 64 false wGninthN6nXL wGninthN6nXW = 4055040 :=
  OctadDense.octSumZ_of_chk 64 6 false wGninthN6nXL wGninthN6nXW _ _ 4055040 wGninthN6nX_Lsh
      wGninthN6nX_Wsh wGninthN6nX_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGninthN6nX_selfchk : OctadDense.selfOctChk 64 [(wGninthN6nXGT0Labs, wGninthN6nXGT0Nums,
    2048), (wGninthN6nXGT1Labs, wGninthN6nXGT1Nums, 2048), (wGninthN6nXGT2Labs,
    wGninthN6nXGT2Nums, 2048), (wGninthN6nXGT3Labs, wGninthN6nXGT3Nums, 2048),
    (wGninthN6nXGT4Labs, wGninthN6nXGT4Nums, 2048), (wGninthN6nXGT5Labs, wGninthN6nXGT5Nums,
    2048), (wGninthN6nXGT6Labs, wGninthN6nXGT6Nums, 2048), (wGninthN6nXGT7Labs,
    wGninthN6nXGT7Nums, 2048), (wGninthN6nXGT8Labs, wGninthN6nXGT8Nums, 2048),
    (wGninthN6nXGT9Labs, wGninthN6nXGT9Nums, 2048), (wGninthN6nXGT10Labs, wGninthN6nXGT10Nums,
    2048), (wGninthN6nXGT11Labs, wGninthN6nXGT11Nums, 2048), (wGninthN6nXGT12Labs,
    wGninthN6nXGT12Nums, 2048), (wGninthN6nXGT13Labs, wGninthN6nXGT13Nums, 2048),
    (wGninthN6nXGT14Labs, wGninthN6nXGT14Nums, 2048), (wGninthN6nXGT15Labs, wGninthN6nXGT15Nums,
    2048), (wGninthN6nXGT16Labs, wGninthN6nXGT16Nums, 2048), (wGninthN6nXGT17Labs,
    wGninthN6nXGT17Nums, 2048), (wGninthN6nXGT18Labs, wGninthN6nXGT18Nums, 2048),
    (wGninthN6nXGT19Labs, wGninthN6nXGT19Nums, 2048), (wGninthN6nXGT20Labs, wGninthN6nXGT20Nums,
    2048), (wGninthN6nXGT21Labs, wGninthN6nXGT21Nums, 2048), (wGninthN6nXGT22Labs,
    wGninthN6nXGT22Nums, 1704)] 506880 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGninthN6nX_hn : wGninthN6nXL.sden * (octSumZ 64 false wGninthN6nXL wGninthN6nXW : ℚ) / 8 =
    wGninthN6nXW.sden * (selfOctP wGninthN6nXW : ℚ) := by
  rw [wGninthN6nX_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGninthN6nXW _ 506880
      wGninthN6nX_Wsh wGninthN6nX_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
