/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN5nXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM

/-! # Factory parts (octads) of the identification Ninth[7]- <-> Ninth[7]- (record gninth:N5-, e =
-1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGninthN5nX_chk : OctadDense.octSumChk 64 6 false [(wGninthN5nXHT0Labs,
    wGninthN5nXHT0Nums, 2048), (wGninthN5nXHT1Labs, wGninthN5nXHT1Nums, 2048),
    (wGninthN5nXHT2Labs, wGninthN5nXHT2Nums, 2048), (wGninthN5nXHT3Labs, wGninthN5nXHT3Nums,
    2048), (wGninthN5nXHT4Labs, wGninthN5nXHT4Nums, 2048), (wGninthN5nXHT5Labs,
    wGninthN5nXHT5Nums, 2048), (wGninthN5nXHT6Labs, wGninthN5nXHT6Nums, 2048),
    (wGninthN5nXHT7Labs, wGninthN5nXHT7Nums, 2048), (wGninthN5nXHT8Labs, wGninthN5nXHT8Nums,
    2048), (wGninthN5nXHT9Labs, wGninthN5nXHT9Nums, 2048), (wGninthN5nXHT10Labs,
    wGninthN5nXHT10Nums, 2048), (wGninthN5nXHT11Labs, wGninthN5nXHT11Nums, 2048),
    (wGninthN5nXHT12Labs, wGninthN5nXHT12Nums, 2048), (wGninthN5nXHT13Labs, wGninthN5nXHT13Nums,
    2048), (wGninthN5nXHT14Labs, wGninthN5nXHT14Nums, 2048), (wGninthN5nXHT15Labs,
    wGninthN5nXHT15Nums, 2048), (wGninthN5nXHT16Labs, wGninthN5nXHT16Nums, 2048),
    (wGninthN5nXHT17Labs, wGninthN5nXHT17Nums, 2048), (wGninthN5nXHT18Labs, wGninthN5nXHT18Nums,
    2048), (wGninthN5nXHT19Labs, wGninthN5nXHT19Nums, 2048), (wGninthN5nXHT20Labs,
    wGninthN5nXHT20Nums, 2048), (wGninthN5nXHT21Labs, wGninthN5nXHT21Nums, 2048),
    (wGninthN5nXHT22Labs, wGninthN5nXHT22Nums, 2048), (wGninthN5nXHT23Labs, wGninthN5nXHT23Nums,
    2048), (wGninthN5nXHT24Labs, wGninthN5nXHT24Nums, 2048), (wGninthN5nXHT25Labs,
    wGninthN5nXHT25Nums, 2048), (wGninthN5nXHT26Labs, wGninthN5nXHT26Nums, 2048),
    (wGninthN5nXHT27Labs, wGninthN5nXHT27Nums, 2048), (wGninthN5nXHT28Labs, wGninthN5nXHT28Nums,
    2048), (wGninthN5nXHT29Labs, wGninthN5nXHT29Nums, 2048), (wGninthN5nXHT30Labs,
    wGninthN5nXHT30Nums, 144)] [(wGninthN5nXGT0Labs, wGninthN5nXGT0Nums, 2048),
    (wGninthN5nXGT1Labs, wGninthN5nXGT1Nums, 2048), (wGninthN5nXGT2Labs, wGninthN5nXGT2Nums,
    2048), (wGninthN5nXGT3Labs, wGninthN5nXGT3Nums, 2048), (wGninthN5nXGT4Labs,
    wGninthN5nXGT4Nums, 2048), (wGninthN5nXGT5Labs, wGninthN5nXGT5Nums, 2048),
    (wGninthN5nXGT6Labs, wGninthN5nXGT6Nums, 2048), (wGninthN5nXGT7Labs, wGninthN5nXGT7Nums,
    2048), (wGninthN5nXGT8Labs, wGninthN5nXGT8Nums, 2048), (wGninthN5nXGT9Labs,
    wGninthN5nXGT9Nums, 2048), (wGninthN5nXGT10Labs, wGninthN5nXGT10Nums, 2048),
    (wGninthN5nXGT11Labs, wGninthN5nXGT11Nums, 2048), (wGninthN5nXGT12Labs, wGninthN5nXGT12Nums,
    2048), (wGninthN5nXGT13Labs, wGninthN5nXGT13Nums, 2048), (wGninthN5nXGT14Labs,
    wGninthN5nXGT14Nums, 2048), (wGninthN5nXGT15Labs, wGninthN5nXGT15Nums, 2048),
    (wGninthN5nXGT16Labs, wGninthN5nXGT16Nums, 2048), (wGninthN5nXGT17Labs, wGninthN5nXGT17Nums,
    2048), (wGninthN5nXGT18Labs, wGninthN5nXGT18Nums, 2048), (wGninthN5nXGT19Labs,
    wGninthN5nXGT19Nums, 2048), (wGninthN5nXGT20Labs, wGninthN5nXGT20Nums, 2048),
    (wGninthN5nXGT21Labs, wGninthN5nXGT21Nums, 2048), (wGninthN5nXGT22Labs, wGninthN5nXGT22Nums,
    2048), (wGninthN5nXGT23Labs, wGninthN5nXGT23Nums, 2048), (wGninthN5nXGT24Labs,
    wGninthN5nXGT24Nums, 2048), (wGninthN5nXGT25Labs, wGninthN5nXGT25Nums, 2048),
    (wGninthN5nXGT26Labs, wGninthN5nXGT26Nums, 2048), (wGninthN5nXGT27Labs, wGninthN5nXGT27Nums,
    2048), (wGninthN5nXGT28Labs, wGninthN5nXGT28Nums, 2048), (wGninthN5nXGT29Labs,
    wGninthN5nXGT29Nums, 2048), (wGninthN5nXGT30Labs, wGninthN5nXGT30Nums, 144)] 4050944 = true :=
    by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGninthN5nX_Lsh : wGninthN5nXL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN5nXHT0Labs, wGninthN5nXHT0Nums, 2048), (wGninthN5nXHT1Labs, wGninthN5nXHT1Nums,
    2048), (wGninthN5nXHT2Labs, wGninthN5nXHT2Nums, 2048), (wGninthN5nXHT3Labs,
    wGninthN5nXHT3Nums, 2048), (wGninthN5nXHT4Labs, wGninthN5nXHT4Nums, 2048),
    (wGninthN5nXHT5Labs, wGninthN5nXHT5Nums, 2048), (wGninthN5nXHT6Labs, wGninthN5nXHT6Nums,
    2048), (wGninthN5nXHT7Labs, wGninthN5nXHT7Nums, 2048), (wGninthN5nXHT8Labs,
    wGninthN5nXHT8Nums, 2048), (wGninthN5nXHT9Labs, wGninthN5nXHT9Nums, 2048),
    (wGninthN5nXHT10Labs, wGninthN5nXHT10Nums, 2048), (wGninthN5nXHT11Labs, wGninthN5nXHT11Nums,
    2048), (wGninthN5nXHT12Labs, wGninthN5nXHT12Nums, 2048), (wGninthN5nXHT13Labs,
    wGninthN5nXHT13Nums, 2048), (wGninthN5nXHT14Labs, wGninthN5nXHT14Nums, 2048),
    (wGninthN5nXHT15Labs, wGninthN5nXHT15Nums, 2048), (wGninthN5nXHT16Labs, wGninthN5nXHT16Nums,
    2048), (wGninthN5nXHT17Labs, wGninthN5nXHT17Nums, 2048), (wGninthN5nXHT18Labs,
    wGninthN5nXHT18Nums, 2048), (wGninthN5nXHT19Labs, wGninthN5nXHT19Nums, 2048),
    (wGninthN5nXHT20Labs, wGninthN5nXHT20Nums, 2048), (wGninthN5nXHT21Labs, wGninthN5nXHT21Nums,
    2048), (wGninthN5nXHT22Labs, wGninthN5nXHT22Nums, 2048), (wGninthN5nXHT23Labs,
    wGninthN5nXHT23Nums, 2048), (wGninthN5nXHT24Labs, wGninthN5nXHT24Nums, 2048),
    (wGninthN5nXHT25Labs, wGninthN5nXHT25Nums, 2048), (wGninthN5nXHT26Labs, wGninthN5nXHT26Nums,
    2048), (wGninthN5nXHT27Labs, wGninthN5nXHT27Nums, 2048), (wGninthN5nXHT28Labs,
    wGninthN5nXHT28Nums, 2048), (wGninthN5nXHT29Labs, wGninthN5nXHT29Nums, 2048),
    (wGninthN5nXHT30Labs, wGninthN5nXHT30Nums, 144)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGninthN5nX_Wsh : wGninthN5nXW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN5nXGT0Labs, wGninthN5nXGT0Nums, 2048), (wGninthN5nXGT1Labs, wGninthN5nXGT1Nums,
    2048), (wGninthN5nXGT2Labs, wGninthN5nXGT2Nums, 2048), (wGninthN5nXGT3Labs,
    wGninthN5nXGT3Nums, 2048), (wGninthN5nXGT4Labs, wGninthN5nXGT4Nums, 2048),
    (wGninthN5nXGT5Labs, wGninthN5nXGT5Nums, 2048), (wGninthN5nXGT6Labs, wGninthN5nXGT6Nums,
    2048), (wGninthN5nXGT7Labs, wGninthN5nXGT7Nums, 2048), (wGninthN5nXGT8Labs,
    wGninthN5nXGT8Nums, 2048), (wGninthN5nXGT9Labs, wGninthN5nXGT9Nums, 2048),
    (wGninthN5nXGT10Labs, wGninthN5nXGT10Nums, 2048), (wGninthN5nXGT11Labs, wGninthN5nXGT11Nums,
    2048), (wGninthN5nXGT12Labs, wGninthN5nXGT12Nums, 2048), (wGninthN5nXGT13Labs,
    wGninthN5nXGT13Nums, 2048), (wGninthN5nXGT14Labs, wGninthN5nXGT14Nums, 2048),
    (wGninthN5nXGT15Labs, wGninthN5nXGT15Nums, 2048), (wGninthN5nXGT16Labs, wGninthN5nXGT16Nums,
    2048), (wGninthN5nXGT17Labs, wGninthN5nXGT17Nums, 2048), (wGninthN5nXGT18Labs,
    wGninthN5nXGT18Nums, 2048), (wGninthN5nXGT19Labs, wGninthN5nXGT19Nums, 2048),
    (wGninthN5nXGT20Labs, wGninthN5nXGT20Nums, 2048), (wGninthN5nXGT21Labs, wGninthN5nXGT21Nums,
    2048), (wGninthN5nXGT22Labs, wGninthN5nXGT22Nums, 2048), (wGninthN5nXGT23Labs,
    wGninthN5nXGT23Nums, 2048), (wGninthN5nXGT24Labs, wGninthN5nXGT24Nums, 2048),
    (wGninthN5nXGT25Labs, wGninthN5nXGT25Nums, 2048), (wGninthN5nXGT26Labs, wGninthN5nXGT26Nums,
    2048), (wGninthN5nXGT27Labs, wGninthN5nXGT27Nums, 2048), (wGninthN5nXGT28Labs,
    wGninthN5nXGT28Nums, 2048), (wGninthN5nXGT29Labs, wGninthN5nXGT29Nums, 2048),
    (wGninthN5nXGT30Labs, wGninthN5nXGT30Nums, 144)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGninthN5nX_hok : octPackOk 64 wGninthN5nXL = true :=
  OctadDense.octPackOk_of_chk 64 6 false wGninthN5nXL _ _ 4050944 wGninthN5nX_Lsh wGninthN5nX_chk

/-- The octad integer sum. -/
theorem wGninthN5nX_octn : octSumZ 64 false wGninthN5nXL wGninthN5nXW = 4050944 :=
  OctadDense.octSumZ_of_chk 64 6 false wGninthN5nXL wGninthN5nXW _ _ 4050944 wGninthN5nX_Lsh
      wGninthN5nX_Wsh wGninthN5nX_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGninthN5nX_selfchk : OctadDense.selfOctChk 64 [(wGninthN5nXGT0Labs, wGninthN5nXGT0Nums,
    2048), (wGninthN5nXGT1Labs, wGninthN5nXGT1Nums, 2048), (wGninthN5nXGT2Labs,
    wGninthN5nXGT2Nums, 2048), (wGninthN5nXGT3Labs, wGninthN5nXGT3Nums, 2048),
    (wGninthN5nXGT4Labs, wGninthN5nXGT4Nums, 2048), (wGninthN5nXGT5Labs, wGninthN5nXGT5Nums,
    2048), (wGninthN5nXGT6Labs, wGninthN5nXGT6Nums, 2048), (wGninthN5nXGT7Labs,
    wGninthN5nXGT7Nums, 2048), (wGninthN5nXGT8Labs, wGninthN5nXGT8Nums, 2048),
    (wGninthN5nXGT9Labs, wGninthN5nXGT9Nums, 2048), (wGninthN5nXGT10Labs, wGninthN5nXGT10Nums,
    2048), (wGninthN5nXGT11Labs, wGninthN5nXGT11Nums, 2048), (wGninthN5nXGT12Labs,
    wGninthN5nXGT12Nums, 2048), (wGninthN5nXGT13Labs, wGninthN5nXGT13Nums, 2048),
    (wGninthN5nXGT14Labs, wGninthN5nXGT14Nums, 2048), (wGninthN5nXGT15Labs, wGninthN5nXGT15Nums,
    2048), (wGninthN5nXGT16Labs, wGninthN5nXGT16Nums, 2048), (wGninthN5nXGT17Labs,
    wGninthN5nXGT17Nums, 2048), (wGninthN5nXGT18Labs, wGninthN5nXGT18Nums, 2048),
    (wGninthN5nXGT19Labs, wGninthN5nXGT19Nums, 2048), (wGninthN5nXGT20Labs, wGninthN5nXGT20Nums,
    2048), (wGninthN5nXGT21Labs, wGninthN5nXGT21Nums, 2048), (wGninthN5nXGT22Labs,
    wGninthN5nXGT22Nums, 2048), (wGninthN5nXGT23Labs, wGninthN5nXGT23Nums, 2048),
    (wGninthN5nXGT24Labs, wGninthN5nXGT24Nums, 2048), (wGninthN5nXGT25Labs, wGninthN5nXGT25Nums,
    2048), (wGninthN5nXGT26Labs, wGninthN5nXGT26Nums, 2048), (wGninthN5nXGT27Labs,
    wGninthN5nXGT27Nums, 2048), (wGninthN5nXGT28Labs, wGninthN5nXGT28Nums, 2048),
    (wGninthN5nXGT29Labs, wGninthN5nXGT29Nums, 2048), (wGninthN5nXGT30Labs, wGninthN5nXGT30Nums,
    144)] 506368 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGninthN5nX_hn : wGninthN5nXL.sden * (octSumZ 64 false wGninthN5nXL wGninthN5nXW : ℚ) / 8 =
    wGninthN5nXW.sden * (selfOctP wGninthN5nXW : ℚ) := by
  rw [wGninthN5nX_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGninthN5nXW _ 506368
      wGninthN5nX_Wsh wGninthN5nX_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
