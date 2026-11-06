/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN4pXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octads) of the identification Ninth[6]+ <-> Tenth[74]- (record gninth:N4+, e
= 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGninthN4pX_chk : OctadDense.octSumChk 64 6 true [(wGninthN4pXHT0Labs, wGninthN4pXHT0Nums,
    2048), (wGninthN4pXHT1Labs, wGninthN4pXHT1Nums, 2048), (wGninthN4pXHT2Labs,
    wGninthN4pXHT2Nums, 2048), (wGninthN4pXHT3Labs, wGninthN4pXHT3Nums, 2048),
    (wGninthN4pXHT4Labs, wGninthN4pXHT4Nums, 2048), (wGninthN4pXHT5Labs, wGninthN4pXHT5Nums,
    2048), (wGninthN4pXHT6Labs, wGninthN4pXHT6Nums, 2048), (wGninthN4pXHT7Labs,
    wGninthN4pXHT7Nums, 2048), (wGninthN4pXHT8Labs, wGninthN4pXHT8Nums, 2048),
    (wGninthN4pXHT9Labs, wGninthN4pXHT9Nums, 2048), (wGninthN4pXHT10Labs, wGninthN4pXHT10Nums,
    2048), (wGninthN4pXHT11Labs, wGninthN4pXHT11Nums, 2048), (wGninthN4pXHT12Labs,
    wGninthN4pXHT12Nums, 2048), (wGninthN4pXHT13Labs, wGninthN4pXHT13Nums, 2048),
    (wGninthN4pXHT14Labs, wGninthN4pXHT14Nums, 2048), (wGninthN4pXHT15Labs, wGninthN4pXHT15Nums,
    2048), (wGninthN4pXHT16Labs, wGninthN4pXHT16Nums, 2048), (wGninthN4pXHT17Labs,
    wGninthN4pXHT17Nums, 2048), (wGninthN4pXHT18Labs, wGninthN4pXHT18Nums, 2048),
    (wGninthN4pXHT19Labs, wGninthN4pXHT19Nums, 2048), (wGninthN4pXHT20Labs, wGninthN4pXHT20Nums,
    2048), (wGninthN4pXHT21Labs, wGninthN4pXHT21Nums, 2048), (wGninthN4pXHT22Labs,
    wGninthN4pXHT22Nums, 2048), (wGninthN4pXHT23Labs, wGninthN4pXHT23Nums, 2048),
    (wGninthN4pXHT24Labs, wGninthN4pXHT24Nums, 2048), (wGninthN4pXHT25Labs, wGninthN4pXHT25Nums,
    2048), (wGninthN4pXHT26Labs, wGninthN4pXHT26Nums, 2048), (wGninthN4pXHT27Labs,
    wGninthN4pXHT27Nums, 2048), (wGninthN4pXHT28Labs, wGninthN4pXHT28Nums, 2048),
    (wGninthN4pXHT29Labs, wGninthN4pXHT29Nums, 2048), (wGninthN4pXHT30Labs, wGninthN4pXHT30Nums,
    144)] [(wGninthN4pXGT0Labs, wGninthN4pXGT0Nums, 2048), (wGninthN4pXGT1Labs,
    wGninthN4pXGT1Nums, 2048), (wGninthN4pXGT2Labs, wGninthN4pXGT2Nums, 2048),
    (wGninthN4pXGT3Labs, wGninthN4pXGT3Nums, 2048), (wGninthN4pXGT4Labs, wGninthN4pXGT4Nums,
    2048), (wGninthN4pXGT5Labs, wGninthN4pXGT5Nums, 2048), (wGninthN4pXGT6Labs,
    wGninthN4pXGT6Nums, 2048), (wGninthN4pXGT7Labs, wGninthN4pXGT7Nums, 2048),
    (wGninthN4pXGT8Labs, wGninthN4pXGT8Nums, 2048), (wGninthN4pXGT9Labs, wGninthN4pXGT9Nums,
    2048), (wGninthN4pXGT10Labs, wGninthN4pXGT10Nums, 2048), (wGninthN4pXGT11Labs,
    wGninthN4pXGT11Nums, 2048), (wGninthN4pXGT12Labs, wGninthN4pXGT12Nums, 2048),
    (wGninthN4pXGT13Labs, wGninthN4pXGT13Nums, 2048), (wGninthN4pXGT14Labs, wGninthN4pXGT14Nums,
    2048), (wGninthN4pXGT15Labs, wGninthN4pXGT15Nums, 2048), (wGninthN4pXGT16Labs,
    wGninthN4pXGT16Nums, 2048), (wGninthN4pXGT17Labs, wGninthN4pXGT17Nums, 2048),
    (wGninthN4pXGT18Labs, wGninthN4pXGT18Nums, 2048), (wGninthN4pXGT19Labs, wGninthN4pXGT19Nums,
    2048), (wGninthN4pXGT20Labs, wGninthN4pXGT20Nums, 2048), (wGninthN4pXGT21Labs,
    wGninthN4pXGT21Nums, 2048), (wGninthN4pXGT22Labs, wGninthN4pXGT22Nums, 1026)] 4018176 = true
    := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGninthN4pX_Lsh : wGninthN4pXL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN4pXHT0Labs, wGninthN4pXHT0Nums, 2048), (wGninthN4pXHT1Labs, wGninthN4pXHT1Nums,
    2048), (wGninthN4pXHT2Labs, wGninthN4pXHT2Nums, 2048), (wGninthN4pXHT3Labs,
    wGninthN4pXHT3Nums, 2048), (wGninthN4pXHT4Labs, wGninthN4pXHT4Nums, 2048),
    (wGninthN4pXHT5Labs, wGninthN4pXHT5Nums, 2048), (wGninthN4pXHT6Labs, wGninthN4pXHT6Nums,
    2048), (wGninthN4pXHT7Labs, wGninthN4pXHT7Nums, 2048), (wGninthN4pXHT8Labs,
    wGninthN4pXHT8Nums, 2048), (wGninthN4pXHT9Labs, wGninthN4pXHT9Nums, 2048),
    (wGninthN4pXHT10Labs, wGninthN4pXHT10Nums, 2048), (wGninthN4pXHT11Labs, wGninthN4pXHT11Nums,
    2048), (wGninthN4pXHT12Labs, wGninthN4pXHT12Nums, 2048), (wGninthN4pXHT13Labs,
    wGninthN4pXHT13Nums, 2048), (wGninthN4pXHT14Labs, wGninthN4pXHT14Nums, 2048),
    (wGninthN4pXHT15Labs, wGninthN4pXHT15Nums, 2048), (wGninthN4pXHT16Labs, wGninthN4pXHT16Nums,
    2048), (wGninthN4pXHT17Labs, wGninthN4pXHT17Nums, 2048), (wGninthN4pXHT18Labs,
    wGninthN4pXHT18Nums, 2048), (wGninthN4pXHT19Labs, wGninthN4pXHT19Nums, 2048),
    (wGninthN4pXHT20Labs, wGninthN4pXHT20Nums, 2048), (wGninthN4pXHT21Labs, wGninthN4pXHT21Nums,
    2048), (wGninthN4pXHT22Labs, wGninthN4pXHT22Nums, 2048), (wGninthN4pXHT23Labs,
    wGninthN4pXHT23Nums, 2048), (wGninthN4pXHT24Labs, wGninthN4pXHT24Nums, 2048),
    (wGninthN4pXHT25Labs, wGninthN4pXHT25Nums, 2048), (wGninthN4pXHT26Labs, wGninthN4pXHT26Nums,
    2048), (wGninthN4pXHT27Labs, wGninthN4pXHT27Nums, 2048), (wGninthN4pXHT28Labs,
    wGninthN4pXHT28Nums, 2048), (wGninthN4pXHT29Labs, wGninthN4pXHT29Nums, 2048),
    (wGninthN4pXHT30Labs, wGninthN4pXHT30Nums, 144)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGninthN4pX_Wsh : wGninthN4pXW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN4pXGT0Labs, wGninthN4pXGT0Nums, 2048), (wGninthN4pXGT1Labs, wGninthN4pXGT1Nums,
    2048), (wGninthN4pXGT2Labs, wGninthN4pXGT2Nums, 2048), (wGninthN4pXGT3Labs,
    wGninthN4pXGT3Nums, 2048), (wGninthN4pXGT4Labs, wGninthN4pXGT4Nums, 2048),
    (wGninthN4pXGT5Labs, wGninthN4pXGT5Nums, 2048), (wGninthN4pXGT6Labs, wGninthN4pXGT6Nums,
    2048), (wGninthN4pXGT7Labs, wGninthN4pXGT7Nums, 2048), (wGninthN4pXGT8Labs,
    wGninthN4pXGT8Nums, 2048), (wGninthN4pXGT9Labs, wGninthN4pXGT9Nums, 2048),
    (wGninthN4pXGT10Labs, wGninthN4pXGT10Nums, 2048), (wGninthN4pXGT11Labs, wGninthN4pXGT11Nums,
    2048), (wGninthN4pXGT12Labs, wGninthN4pXGT12Nums, 2048), (wGninthN4pXGT13Labs,
    wGninthN4pXGT13Nums, 2048), (wGninthN4pXGT14Labs, wGninthN4pXGT14Nums, 2048),
    (wGninthN4pXGT15Labs, wGninthN4pXGT15Nums, 2048), (wGninthN4pXGT16Labs, wGninthN4pXGT16Nums,
    2048), (wGninthN4pXGT17Labs, wGninthN4pXGT17Nums, 2048), (wGninthN4pXGT18Labs,
    wGninthN4pXGT18Nums, 2048), (wGninthN4pXGT19Labs, wGninthN4pXGT19Nums, 2048),
    (wGninthN4pXGT20Labs, wGninthN4pXGT20Nums, 2048), (wGninthN4pXGT21Labs, wGninthN4pXGT21Nums,
    2048), (wGninthN4pXGT22Labs, wGninthN4pXGT22Nums, 1026)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGninthN4pX_hok : octPackOk 64 wGninthN4pXL = true :=
  OctadDense.octPackOk_of_chk 64 6 true wGninthN4pXL _ _ 4018176 wGninthN4pX_Lsh wGninthN4pX_chk

/-- The octad integer sum. -/
theorem wGninthN4pX_octn : octSumZ 64 true wGninthN4pXL wGninthN4pXW = 4018176 :=
  OctadDense.octSumZ_of_chk 64 6 true wGninthN4pXL wGninthN4pXW _ _ 4018176 wGninthN4pX_Lsh
      wGninthN4pX_Wsh wGninthN4pX_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGninthN4pX_selfchk : OctadDense.selfOctChk 64 [(wGninthN4pXGT0Labs, wGninthN4pXGT0Nums,
    2048), (wGninthN4pXGT1Labs, wGninthN4pXGT1Nums, 2048), (wGninthN4pXGT2Labs,
    wGninthN4pXGT2Nums, 2048), (wGninthN4pXGT3Labs, wGninthN4pXGT3Nums, 2048),
    (wGninthN4pXGT4Labs, wGninthN4pXGT4Nums, 2048), (wGninthN4pXGT5Labs, wGninthN4pXGT5Nums,
    2048), (wGninthN4pXGT6Labs, wGninthN4pXGT6Nums, 2048), (wGninthN4pXGT7Labs,
    wGninthN4pXGT7Nums, 2048), (wGninthN4pXGT8Labs, wGninthN4pXGT8Nums, 2048),
    (wGninthN4pXGT9Labs, wGninthN4pXGT9Nums, 2048), (wGninthN4pXGT10Labs, wGninthN4pXGT10Nums,
    2048), (wGninthN4pXGT11Labs, wGninthN4pXGT11Nums, 2048), (wGninthN4pXGT12Labs,
    wGninthN4pXGT12Nums, 2048), (wGninthN4pXGT13Labs, wGninthN4pXGT13Nums, 2048),
    (wGninthN4pXGT14Labs, wGninthN4pXGT14Nums, 2048), (wGninthN4pXGT15Labs, wGninthN4pXGT15Nums,
    2048), (wGninthN4pXGT16Labs, wGninthN4pXGT16Nums, 2048), (wGninthN4pXGT17Labs,
    wGninthN4pXGT17Nums, 2048), (wGninthN4pXGT18Labs, wGninthN4pXGT18Nums, 2048),
    (wGninthN4pXGT19Labs, wGninthN4pXGT19Nums, 2048), (wGninthN4pXGT20Labs, wGninthN4pXGT20Nums,
    2048), (wGninthN4pXGT21Labs, wGninthN4pXGT21Nums, 2048), (wGninthN4pXGT22Labs,
    wGninthN4pXGT22Nums, 1026)] 502272 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGninthN4pX_hn : wGninthN4pXL.sden * (octSumZ 64 true wGninthN4pXL wGninthN4pXW : ℚ) / 8 =
    wGninthN4pXW.sden * (selfOctP wGninthN4pXW : ℚ) := by
  rw [wGninthN4pX_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGninthN4pXW _ 502272
      wGninthN4pX_Wsh wGninthN4pX_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
