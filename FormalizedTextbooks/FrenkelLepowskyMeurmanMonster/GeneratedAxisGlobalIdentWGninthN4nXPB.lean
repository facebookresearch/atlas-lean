/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN4nXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octads) of the identification Ninth[6]- <-> Tenth[74]- (record gninth:N4-, e
= -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGninthN4nX_chk : OctadDense.octSumChk 64 6 false [(wGninthN4nXHT0Labs,
    wGninthN4nXHT0Nums, 2048), (wGninthN4nXHT1Labs, wGninthN4nXHT1Nums, 2048),
    (wGninthN4nXHT2Labs, wGninthN4nXHT2Nums, 2048), (wGninthN4nXHT3Labs, wGninthN4nXHT3Nums,
    2048), (wGninthN4nXHT4Labs, wGninthN4nXHT4Nums, 2048), (wGninthN4nXHT5Labs,
    wGninthN4nXHT5Nums, 2048), (wGninthN4nXHT6Labs, wGninthN4nXHT6Nums, 2048),
    (wGninthN4nXHT7Labs, wGninthN4nXHT7Nums, 2048), (wGninthN4nXHT8Labs, wGninthN4nXHT8Nums,
    2048), (wGninthN4nXHT9Labs, wGninthN4nXHT9Nums, 2048), (wGninthN4nXHT10Labs,
    wGninthN4nXHT10Nums, 2048), (wGninthN4nXHT11Labs, wGninthN4nXHT11Nums, 2048),
    (wGninthN4nXHT12Labs, wGninthN4nXHT12Nums, 2048), (wGninthN4nXHT13Labs, wGninthN4nXHT13Nums,
    2048), (wGninthN4nXHT14Labs, wGninthN4nXHT14Nums, 2048), (wGninthN4nXHT15Labs,
    wGninthN4nXHT15Nums, 2048), (wGninthN4nXHT16Labs, wGninthN4nXHT16Nums, 2048),
    (wGninthN4nXHT17Labs, wGninthN4nXHT17Nums, 2048), (wGninthN4nXHT18Labs, wGninthN4nXHT18Nums,
    2048), (wGninthN4nXHT19Labs, wGninthN4nXHT19Nums, 2048), (wGninthN4nXHT20Labs,
    wGninthN4nXHT20Nums, 2048), (wGninthN4nXHT21Labs, wGninthN4nXHT21Nums, 2048),
    (wGninthN4nXHT22Labs, wGninthN4nXHT22Nums, 2048), (wGninthN4nXHT23Labs, wGninthN4nXHT23Nums,
    2048), (wGninthN4nXHT24Labs, wGninthN4nXHT24Nums, 2048), (wGninthN4nXHT25Labs,
    wGninthN4nXHT25Nums, 2048), (wGninthN4nXHT26Labs, wGninthN4nXHT26Nums, 2048),
    (wGninthN4nXHT27Labs, wGninthN4nXHT27Nums, 2048), (wGninthN4nXHT28Labs, wGninthN4nXHT28Nums,
    2048), (wGninthN4nXHT29Labs, wGninthN4nXHT29Nums, 2048), (wGninthN4nXHT30Labs,
    wGninthN4nXHT30Nums, 144)] [(wGninthN4nXGT0Labs, wGninthN4nXGT0Nums, 2048),
    (wGninthN4nXGT1Labs, wGninthN4nXGT1Nums, 2048), (wGninthN4nXGT2Labs, wGninthN4nXGT2Nums,
    2048), (wGninthN4nXGT3Labs, wGninthN4nXGT3Nums, 2048), (wGninthN4nXGT4Labs,
    wGninthN4nXGT4Nums, 2048), (wGninthN4nXGT5Labs, wGninthN4nXGT5Nums, 2048),
    (wGninthN4nXGT6Labs, wGninthN4nXGT6Nums, 2048), (wGninthN4nXGT7Labs, wGninthN4nXGT7Nums,
    2048), (wGninthN4nXGT8Labs, wGninthN4nXGT8Nums, 2048), (wGninthN4nXGT9Labs,
    wGninthN4nXGT9Nums, 2048), (wGninthN4nXGT10Labs, wGninthN4nXGT10Nums, 2048),
    (wGninthN4nXGT11Labs, wGninthN4nXGT11Nums, 2048), (wGninthN4nXGT12Labs, wGninthN4nXGT12Nums,
    2048), (wGninthN4nXGT13Labs, wGninthN4nXGT13Nums, 2048), (wGninthN4nXGT14Labs,
    wGninthN4nXGT14Nums, 2048), (wGninthN4nXGT15Labs, wGninthN4nXGT15Nums, 2048),
    (wGninthN4nXGT16Labs, wGninthN4nXGT16Nums, 2048), (wGninthN4nXGT17Labs, wGninthN4nXGT17Nums,
    2048), (wGninthN4nXGT18Labs, wGninthN4nXGT18Nums, 2048), (wGninthN4nXGT19Labs,
    wGninthN4nXGT19Nums, 2048), (wGninthN4nXGT20Labs, wGninthN4nXGT20Nums, 2048),
    (wGninthN4nXGT21Labs, wGninthN4nXGT21Nums, 2048), (wGninthN4nXGT22Labs, wGninthN4nXGT22Nums,
    1026)] 4018176 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGninthN4nX_Lsh : wGninthN4nXL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN4nXHT0Labs, wGninthN4nXHT0Nums, 2048), (wGninthN4nXHT1Labs, wGninthN4nXHT1Nums,
    2048), (wGninthN4nXHT2Labs, wGninthN4nXHT2Nums, 2048), (wGninthN4nXHT3Labs,
    wGninthN4nXHT3Nums, 2048), (wGninthN4nXHT4Labs, wGninthN4nXHT4Nums, 2048),
    (wGninthN4nXHT5Labs, wGninthN4nXHT5Nums, 2048), (wGninthN4nXHT6Labs, wGninthN4nXHT6Nums,
    2048), (wGninthN4nXHT7Labs, wGninthN4nXHT7Nums, 2048), (wGninthN4nXHT8Labs,
    wGninthN4nXHT8Nums, 2048), (wGninthN4nXHT9Labs, wGninthN4nXHT9Nums, 2048),
    (wGninthN4nXHT10Labs, wGninthN4nXHT10Nums, 2048), (wGninthN4nXHT11Labs, wGninthN4nXHT11Nums,
    2048), (wGninthN4nXHT12Labs, wGninthN4nXHT12Nums, 2048), (wGninthN4nXHT13Labs,
    wGninthN4nXHT13Nums, 2048), (wGninthN4nXHT14Labs, wGninthN4nXHT14Nums, 2048),
    (wGninthN4nXHT15Labs, wGninthN4nXHT15Nums, 2048), (wGninthN4nXHT16Labs, wGninthN4nXHT16Nums,
    2048), (wGninthN4nXHT17Labs, wGninthN4nXHT17Nums, 2048), (wGninthN4nXHT18Labs,
    wGninthN4nXHT18Nums, 2048), (wGninthN4nXHT19Labs, wGninthN4nXHT19Nums, 2048),
    (wGninthN4nXHT20Labs, wGninthN4nXHT20Nums, 2048), (wGninthN4nXHT21Labs, wGninthN4nXHT21Nums,
    2048), (wGninthN4nXHT22Labs, wGninthN4nXHT22Nums, 2048), (wGninthN4nXHT23Labs,
    wGninthN4nXHT23Nums, 2048), (wGninthN4nXHT24Labs, wGninthN4nXHT24Nums, 2048),
    (wGninthN4nXHT25Labs, wGninthN4nXHT25Nums, 2048), (wGninthN4nXHT26Labs, wGninthN4nXHT26Nums,
    2048), (wGninthN4nXHT27Labs, wGninthN4nXHT27Nums, 2048), (wGninthN4nXHT28Labs,
    wGninthN4nXHT28Nums, 2048), (wGninthN4nXHT29Labs, wGninthN4nXHT29Nums, 2048),
    (wGninthN4nXHT30Labs, wGninthN4nXHT30Nums, 144)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGninthN4nX_Wsh : wGninthN4nXW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN4nXGT0Labs, wGninthN4nXGT0Nums, 2048), (wGninthN4nXGT1Labs, wGninthN4nXGT1Nums,
    2048), (wGninthN4nXGT2Labs, wGninthN4nXGT2Nums, 2048), (wGninthN4nXGT3Labs,
    wGninthN4nXGT3Nums, 2048), (wGninthN4nXGT4Labs, wGninthN4nXGT4Nums, 2048),
    (wGninthN4nXGT5Labs, wGninthN4nXGT5Nums, 2048), (wGninthN4nXGT6Labs, wGninthN4nXGT6Nums,
    2048), (wGninthN4nXGT7Labs, wGninthN4nXGT7Nums, 2048), (wGninthN4nXGT8Labs,
    wGninthN4nXGT8Nums, 2048), (wGninthN4nXGT9Labs, wGninthN4nXGT9Nums, 2048),
    (wGninthN4nXGT10Labs, wGninthN4nXGT10Nums, 2048), (wGninthN4nXGT11Labs, wGninthN4nXGT11Nums,
    2048), (wGninthN4nXGT12Labs, wGninthN4nXGT12Nums, 2048), (wGninthN4nXGT13Labs,
    wGninthN4nXGT13Nums, 2048), (wGninthN4nXGT14Labs, wGninthN4nXGT14Nums, 2048),
    (wGninthN4nXGT15Labs, wGninthN4nXGT15Nums, 2048), (wGninthN4nXGT16Labs, wGninthN4nXGT16Nums,
    2048), (wGninthN4nXGT17Labs, wGninthN4nXGT17Nums, 2048), (wGninthN4nXGT18Labs,
    wGninthN4nXGT18Nums, 2048), (wGninthN4nXGT19Labs, wGninthN4nXGT19Nums, 2048),
    (wGninthN4nXGT20Labs, wGninthN4nXGT20Nums, 2048), (wGninthN4nXGT21Labs, wGninthN4nXGT21Nums,
    2048), (wGninthN4nXGT22Labs, wGninthN4nXGT22Nums, 1026)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGninthN4nX_hok : octPackOk 64 wGninthN4nXL = true :=
  OctadDense.octPackOk_of_chk 64 6 false wGninthN4nXL _ _ 4018176 wGninthN4nX_Lsh wGninthN4nX_chk

/-- The octad integer sum. -/
theorem wGninthN4nX_octn : octSumZ 64 false wGninthN4nXL wGninthN4nXW = 4018176 :=
  OctadDense.octSumZ_of_chk 64 6 false wGninthN4nXL wGninthN4nXW _ _ 4018176 wGninthN4nX_Lsh
      wGninthN4nX_Wsh wGninthN4nX_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGninthN4nX_selfchk : OctadDense.selfOctChk 64 [(wGninthN4nXGT0Labs, wGninthN4nXGT0Nums,
    2048), (wGninthN4nXGT1Labs, wGninthN4nXGT1Nums, 2048), (wGninthN4nXGT2Labs,
    wGninthN4nXGT2Nums, 2048), (wGninthN4nXGT3Labs, wGninthN4nXGT3Nums, 2048),
    (wGninthN4nXGT4Labs, wGninthN4nXGT4Nums, 2048), (wGninthN4nXGT5Labs, wGninthN4nXGT5Nums,
    2048), (wGninthN4nXGT6Labs, wGninthN4nXGT6Nums, 2048), (wGninthN4nXGT7Labs,
    wGninthN4nXGT7Nums, 2048), (wGninthN4nXGT8Labs, wGninthN4nXGT8Nums, 2048),
    (wGninthN4nXGT9Labs, wGninthN4nXGT9Nums, 2048), (wGninthN4nXGT10Labs, wGninthN4nXGT10Nums,
    2048), (wGninthN4nXGT11Labs, wGninthN4nXGT11Nums, 2048), (wGninthN4nXGT12Labs,
    wGninthN4nXGT12Nums, 2048), (wGninthN4nXGT13Labs, wGninthN4nXGT13Nums, 2048),
    (wGninthN4nXGT14Labs, wGninthN4nXGT14Nums, 2048), (wGninthN4nXGT15Labs, wGninthN4nXGT15Nums,
    2048), (wGninthN4nXGT16Labs, wGninthN4nXGT16Nums, 2048), (wGninthN4nXGT17Labs,
    wGninthN4nXGT17Nums, 2048), (wGninthN4nXGT18Labs, wGninthN4nXGT18Nums, 2048),
    (wGninthN4nXGT19Labs, wGninthN4nXGT19Nums, 2048), (wGninthN4nXGT20Labs, wGninthN4nXGT20Nums,
    2048), (wGninthN4nXGT21Labs, wGninthN4nXGT21Nums, 2048), (wGninthN4nXGT22Labs,
    wGninthN4nXGT22Nums, 1026)] 502272 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGninthN4nX_hn : wGninthN4nXL.sden * (octSumZ 64 false wGninthN4nXL wGninthN4nXW : ℚ) / 8 =
    wGninthN4nXW.sden * (selfOctP wGninthN4nXW : ℚ) := by
  rw [wGninthN4nX_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGninthN4nXW _ 502272
      wGninthN4nX_Wsh wGninthN4nX_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
