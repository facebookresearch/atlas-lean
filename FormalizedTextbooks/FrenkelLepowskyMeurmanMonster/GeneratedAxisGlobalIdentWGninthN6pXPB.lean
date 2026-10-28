/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN6pXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (octads) of the identification Ninth[10]+ <-> Twelfth[12]- (record gninth:N6+,
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
theorem wGninthN6pX_chk : OctadDense.octSumChk 64 6 true [(wGninthN6pXHT0Labs, wGninthN6pXHT0Nums,
    2048), (wGninthN6pXHT1Labs, wGninthN6pXHT1Nums, 2048), (wGninthN6pXHT2Labs,
    wGninthN6pXHT2Nums, 2048), (wGninthN6pXHT3Labs, wGninthN6pXHT3Nums, 2048),
    (wGninthN6pXHT4Labs, wGninthN6pXHT4Nums, 2048), (wGninthN6pXHT5Labs, wGninthN6pXHT5Nums,
    2048), (wGninthN6pXHT6Labs, wGninthN6pXHT6Nums, 2048), (wGninthN6pXHT7Labs,
    wGninthN6pXHT7Nums, 2048), (wGninthN6pXHT8Labs, wGninthN6pXHT8Nums, 2048),
    (wGninthN6pXHT9Labs, wGninthN6pXHT9Nums, 2048), (wGninthN6pXHT10Labs, wGninthN6pXHT10Nums,
    2048), (wGninthN6pXHT11Labs, wGninthN6pXHT11Nums, 2048), (wGninthN6pXHT12Labs,
    wGninthN6pXHT12Nums, 2048), (wGninthN6pXHT13Labs, wGninthN6pXHT13Nums, 2048),
    (wGninthN6pXHT14Labs, wGninthN6pXHT14Nums, 2048), (wGninthN6pXHT15Labs, wGninthN6pXHT15Nums,
    2048), (wGninthN6pXHT16Labs, wGninthN6pXHT16Nums, 2048), (wGninthN6pXHT17Labs,
    wGninthN6pXHT17Nums, 2048), (wGninthN6pXHT18Labs, wGninthN6pXHT18Nums, 2048),
    (wGninthN6pXHT19Labs, wGninthN6pXHT19Nums, 2048), (wGninthN6pXHT20Labs, wGninthN6pXHT20Nums,
    2048), (wGninthN6pXHT21Labs, wGninthN6pXHT21Nums, 2048), (wGninthN6pXHT22Labs,
    wGninthN6pXHT22Nums, 2048), (wGninthN6pXHT23Labs, wGninthN6pXHT23Nums, 2048),
    (wGninthN6pXHT24Labs, wGninthN6pXHT24Nums, 2048), (wGninthN6pXHT25Labs, wGninthN6pXHT25Nums,
    2048), (wGninthN6pXHT26Labs, wGninthN6pXHT26Nums, 2048), (wGninthN6pXHT27Labs,
    wGninthN6pXHT27Nums, 2048), (wGninthN6pXHT28Labs, wGninthN6pXHT28Nums, 2048),
    (wGninthN6pXHT29Labs, wGninthN6pXHT29Nums, 2048), (wGninthN6pXHT30Labs, wGninthN6pXHT30Nums,
    144)] [(wGninthN6pXGT0Labs, wGninthN6pXGT0Nums, 2048), (wGninthN6pXGT1Labs,
    wGninthN6pXGT1Nums, 2048), (wGninthN6pXGT2Labs, wGninthN6pXGT2Nums, 2048),
    (wGninthN6pXGT3Labs, wGninthN6pXGT3Nums, 2048), (wGninthN6pXGT4Labs, wGninthN6pXGT4Nums,
    2048), (wGninthN6pXGT5Labs, wGninthN6pXGT5Nums, 2048), (wGninthN6pXGT6Labs,
    wGninthN6pXGT6Nums, 2048), (wGninthN6pXGT7Labs, wGninthN6pXGT7Nums, 2048),
    (wGninthN6pXGT8Labs, wGninthN6pXGT8Nums, 2048), (wGninthN6pXGT9Labs, wGninthN6pXGT9Nums,
    2048), (wGninthN6pXGT10Labs, wGninthN6pXGT10Nums, 2048), (wGninthN6pXGT11Labs,
    wGninthN6pXGT11Nums, 2048), (wGninthN6pXGT12Labs, wGninthN6pXGT12Nums, 2048),
    (wGninthN6pXGT13Labs, wGninthN6pXGT13Nums, 2048), (wGninthN6pXGT14Labs, wGninthN6pXGT14Nums,
    2048), (wGninthN6pXGT15Labs, wGninthN6pXGT15Nums, 2048), (wGninthN6pXGT16Labs,
    wGninthN6pXGT16Nums, 2048), (wGninthN6pXGT17Labs, wGninthN6pXGT17Nums, 2048),
    (wGninthN6pXGT18Labs, wGninthN6pXGT18Nums, 2048), (wGninthN6pXGT19Labs, wGninthN6pXGT19Nums,
    2048), (wGninthN6pXGT20Labs, wGninthN6pXGT20Nums, 2048), (wGninthN6pXGT21Labs,
    wGninthN6pXGT21Nums, 2048), (wGninthN6pXGT22Labs, wGninthN6pXGT22Nums, 1704)] 4055040 = true
    := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGninthN6pX_Lsh : wGninthN6pXL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN6pXHT0Labs, wGninthN6pXHT0Nums, 2048), (wGninthN6pXHT1Labs, wGninthN6pXHT1Nums,
    2048), (wGninthN6pXHT2Labs, wGninthN6pXHT2Nums, 2048), (wGninthN6pXHT3Labs,
    wGninthN6pXHT3Nums, 2048), (wGninthN6pXHT4Labs, wGninthN6pXHT4Nums, 2048),
    (wGninthN6pXHT5Labs, wGninthN6pXHT5Nums, 2048), (wGninthN6pXHT6Labs, wGninthN6pXHT6Nums,
    2048), (wGninthN6pXHT7Labs, wGninthN6pXHT7Nums, 2048), (wGninthN6pXHT8Labs,
    wGninthN6pXHT8Nums, 2048), (wGninthN6pXHT9Labs, wGninthN6pXHT9Nums, 2048),
    (wGninthN6pXHT10Labs, wGninthN6pXHT10Nums, 2048), (wGninthN6pXHT11Labs, wGninthN6pXHT11Nums,
    2048), (wGninthN6pXHT12Labs, wGninthN6pXHT12Nums, 2048), (wGninthN6pXHT13Labs,
    wGninthN6pXHT13Nums, 2048), (wGninthN6pXHT14Labs, wGninthN6pXHT14Nums, 2048),
    (wGninthN6pXHT15Labs, wGninthN6pXHT15Nums, 2048), (wGninthN6pXHT16Labs, wGninthN6pXHT16Nums,
    2048), (wGninthN6pXHT17Labs, wGninthN6pXHT17Nums, 2048), (wGninthN6pXHT18Labs,
    wGninthN6pXHT18Nums, 2048), (wGninthN6pXHT19Labs, wGninthN6pXHT19Nums, 2048),
    (wGninthN6pXHT20Labs, wGninthN6pXHT20Nums, 2048), (wGninthN6pXHT21Labs, wGninthN6pXHT21Nums,
    2048), (wGninthN6pXHT22Labs, wGninthN6pXHT22Nums, 2048), (wGninthN6pXHT23Labs,
    wGninthN6pXHT23Nums, 2048), (wGninthN6pXHT24Labs, wGninthN6pXHT24Nums, 2048),
    (wGninthN6pXHT25Labs, wGninthN6pXHT25Nums, 2048), (wGninthN6pXHT26Labs, wGninthN6pXHT26Nums,
    2048), (wGninthN6pXHT27Labs, wGninthN6pXHT27Nums, 2048), (wGninthN6pXHT28Labs,
    wGninthN6pXHT28Nums, 2048), (wGninthN6pXHT29Labs, wGninthN6pXHT29Nums, 2048),
    (wGninthN6pXHT30Labs, wGninthN6pXHT30Nums, 144)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGninthN6pX_Wsh : wGninthN6pXW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN6pXGT0Labs, wGninthN6pXGT0Nums, 2048), (wGninthN6pXGT1Labs, wGninthN6pXGT1Nums,
    2048), (wGninthN6pXGT2Labs, wGninthN6pXGT2Nums, 2048), (wGninthN6pXGT3Labs,
    wGninthN6pXGT3Nums, 2048), (wGninthN6pXGT4Labs, wGninthN6pXGT4Nums, 2048),
    (wGninthN6pXGT5Labs, wGninthN6pXGT5Nums, 2048), (wGninthN6pXGT6Labs, wGninthN6pXGT6Nums,
    2048), (wGninthN6pXGT7Labs, wGninthN6pXGT7Nums, 2048), (wGninthN6pXGT8Labs,
    wGninthN6pXGT8Nums, 2048), (wGninthN6pXGT9Labs, wGninthN6pXGT9Nums, 2048),
    (wGninthN6pXGT10Labs, wGninthN6pXGT10Nums, 2048), (wGninthN6pXGT11Labs, wGninthN6pXGT11Nums,
    2048), (wGninthN6pXGT12Labs, wGninthN6pXGT12Nums, 2048), (wGninthN6pXGT13Labs,
    wGninthN6pXGT13Nums, 2048), (wGninthN6pXGT14Labs, wGninthN6pXGT14Nums, 2048),
    (wGninthN6pXGT15Labs, wGninthN6pXGT15Nums, 2048), (wGninthN6pXGT16Labs, wGninthN6pXGT16Nums,
    2048), (wGninthN6pXGT17Labs, wGninthN6pXGT17Nums, 2048), (wGninthN6pXGT18Labs,
    wGninthN6pXGT18Nums, 2048), (wGninthN6pXGT19Labs, wGninthN6pXGT19Nums, 2048),
    (wGninthN6pXGT20Labs, wGninthN6pXGT20Nums, 2048), (wGninthN6pXGT21Labs, wGninthN6pXGT21Nums,
    2048), (wGninthN6pXGT22Labs, wGninthN6pXGT22Nums, 1704)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGninthN6pX_hok : octPackOk 64 wGninthN6pXL = true :=
  OctadDense.octPackOk_of_chk 64 6 true wGninthN6pXL _ _ 4055040 wGninthN6pX_Lsh wGninthN6pX_chk

/-- The octad integer sum. -/
theorem wGninthN6pX_octn : octSumZ 64 true wGninthN6pXL wGninthN6pXW = 4055040 :=
  OctadDense.octSumZ_of_chk 64 6 true wGninthN6pXL wGninthN6pXW _ _ 4055040 wGninthN6pX_Lsh
      wGninthN6pX_Wsh wGninthN6pX_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGninthN6pX_selfchk : OctadDense.selfOctChk 64 [(wGninthN6pXGT0Labs, wGninthN6pXGT0Nums,
    2048), (wGninthN6pXGT1Labs, wGninthN6pXGT1Nums, 2048), (wGninthN6pXGT2Labs,
    wGninthN6pXGT2Nums, 2048), (wGninthN6pXGT3Labs, wGninthN6pXGT3Nums, 2048),
    (wGninthN6pXGT4Labs, wGninthN6pXGT4Nums, 2048), (wGninthN6pXGT5Labs, wGninthN6pXGT5Nums,
    2048), (wGninthN6pXGT6Labs, wGninthN6pXGT6Nums, 2048), (wGninthN6pXGT7Labs,
    wGninthN6pXGT7Nums, 2048), (wGninthN6pXGT8Labs, wGninthN6pXGT8Nums, 2048),
    (wGninthN6pXGT9Labs, wGninthN6pXGT9Nums, 2048), (wGninthN6pXGT10Labs, wGninthN6pXGT10Nums,
    2048), (wGninthN6pXGT11Labs, wGninthN6pXGT11Nums, 2048), (wGninthN6pXGT12Labs,
    wGninthN6pXGT12Nums, 2048), (wGninthN6pXGT13Labs, wGninthN6pXGT13Nums, 2048),
    (wGninthN6pXGT14Labs, wGninthN6pXGT14Nums, 2048), (wGninthN6pXGT15Labs, wGninthN6pXGT15Nums,
    2048), (wGninthN6pXGT16Labs, wGninthN6pXGT16Nums, 2048), (wGninthN6pXGT17Labs,
    wGninthN6pXGT17Nums, 2048), (wGninthN6pXGT18Labs, wGninthN6pXGT18Nums, 2048),
    (wGninthN6pXGT19Labs, wGninthN6pXGT19Nums, 2048), (wGninthN6pXGT20Labs, wGninthN6pXGT20Nums,
    2048), (wGninthN6pXGT21Labs, wGninthN6pXGT21Nums, 2048), (wGninthN6pXGT22Labs,
    wGninthN6pXGT22Nums, 1704)] 506880 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGninthN6pX_hn : wGninthN6pXL.sden * (octSumZ 64 true wGninthN6pXL wGninthN6pXW : ℚ) / 8 =
    wGninthN6pXW.sden * (selfOctP wGninthN6pXW : ℚ) := by
  rw [wGninthN6pX_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGninthN6pXW _ 506880
      wGninthN6pX_Wsh wGninthN6pX_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
