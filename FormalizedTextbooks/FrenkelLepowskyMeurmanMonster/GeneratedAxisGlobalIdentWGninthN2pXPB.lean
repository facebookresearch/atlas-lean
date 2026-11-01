/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN2pXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octads) of the identification Ninth[3]+ <-> Tenth[50]+ (record gninth:N2+, e
= 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGninthN2pX_chk : OctadDense.octSumChk 64 7 true [(wGninthN2pXHT0Labs, wGninthN2pXHT0Nums,
    2048), (wGninthN2pXHT1Labs, wGninthN2pXHT1Nums, 2048), (wGninthN2pXHT2Labs,
    wGninthN2pXHT2Nums, 2048), (wGninthN2pXHT3Labs, wGninthN2pXHT3Nums, 2048),
    (wGninthN2pXHT4Labs, wGninthN2pXHT4Nums, 2048), (wGninthN2pXHT5Labs, wGninthN2pXHT5Nums,
    2048), (wGninthN2pXHT6Labs, wGninthN2pXHT6Nums, 2048), (wGninthN2pXHT7Labs,
    wGninthN2pXHT7Nums, 2048), (wGninthN2pXHT8Labs, wGninthN2pXHT8Nums, 2048),
    (wGninthN2pXHT9Labs, wGninthN2pXHT9Nums, 2048), (wGninthN2pXHT10Labs, wGninthN2pXHT10Nums,
    2048), (wGninthN2pXHT11Labs, wGninthN2pXHT11Nums, 2048), (wGninthN2pXHT12Labs,
    wGninthN2pXHT12Nums, 2048), (wGninthN2pXHT13Labs, wGninthN2pXHT13Nums, 2048),
    (wGninthN2pXHT14Labs, wGninthN2pXHT14Nums, 2048), (wGninthN2pXHT15Labs, wGninthN2pXHT15Nums,
    2048), (wGninthN2pXHT16Labs, wGninthN2pXHT16Nums, 2048), (wGninthN2pXHT17Labs,
    wGninthN2pXHT17Nums, 2048), (wGninthN2pXHT18Labs, wGninthN2pXHT18Nums, 2048),
    (wGninthN2pXHT19Labs, wGninthN2pXHT19Nums, 2048), (wGninthN2pXHT20Labs, wGninthN2pXHT20Nums,
    2048), (wGninthN2pXHT21Labs, wGninthN2pXHT21Nums, 2048), (wGninthN2pXHT22Labs,
    wGninthN2pXHT22Nums, 2048), (wGninthN2pXHT23Labs, wGninthN2pXHT23Nums, 2048),
    (wGninthN2pXHT24Labs, wGninthN2pXHT24Nums, 2048), (wGninthN2pXHT25Labs, wGninthN2pXHT25Nums,
    2048), (wGninthN2pXHT26Labs, wGninthN2pXHT26Nums, 2048), (wGninthN2pXHT27Labs,
    wGninthN2pXHT27Nums, 2048), (wGninthN2pXHT28Labs, wGninthN2pXHT28Nums, 2048),
    (wGninthN2pXHT29Labs, wGninthN2pXHT29Nums, 2048), (wGninthN2pXHT30Labs, wGninthN2pXHT30Nums,
    144)] [(wGninthN2pXGT0Labs, wGninthN2pXGT0Nums, 2048), (wGninthN2pXGT1Labs,
    wGninthN2pXGT1Nums, 2048), (wGninthN2pXGT2Labs, wGninthN2pXGT2Nums, 2048),
    (wGninthN2pXGT3Labs, wGninthN2pXGT3Nums, 2048), (wGninthN2pXGT4Labs, wGninthN2pXGT4Nums,
    2048), (wGninthN2pXGT5Labs, wGninthN2pXGT5Nums, 2048), (wGninthN2pXGT6Labs,
    wGninthN2pXGT6Nums, 2048), (wGninthN2pXGT7Labs, wGninthN2pXGT7Nums, 2048),
    (wGninthN2pXGT8Labs, wGninthN2pXGT8Nums, 2048), (wGninthN2pXGT9Labs, wGninthN2pXGT9Nums,
    2048), (wGninthN2pXGT10Labs, wGninthN2pXGT10Nums, 2048), (wGninthN2pXGT11Labs,
    wGninthN2pXGT11Nums, 2048), (wGninthN2pXGT12Labs, wGninthN2pXGT12Nums, 2048),
    (wGninthN2pXGT13Labs, wGninthN2pXGT13Nums, 2048), (wGninthN2pXGT14Labs, wGninthN2pXGT14Nums,
    2048), (wGninthN2pXGT15Labs, wGninthN2pXGT15Nums, 2048), (wGninthN2pXGT16Labs,
    wGninthN2pXGT16Nums, 2048), (wGninthN2pXGT17Labs, wGninthN2pXGT17Nums, 2048),
    (wGninthN2pXGT18Labs, wGninthN2pXGT18Nums, 2048), (wGninthN2pXGT19Labs, wGninthN2pXGT19Nums,
    2048), (wGninthN2pXGT20Labs, wGninthN2pXGT20Nums, 2048), (wGninthN2pXGT21Labs,
    wGninthN2pXGT21Nums, 2048), (wGninthN2pXGT22Labs, wGninthN2pXGT22Nums, 1026)] 4016128 = true
    := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGninthN2pX_Lsh : wGninthN2pXL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN2pXHT0Labs, wGninthN2pXHT0Nums, 2048), (wGninthN2pXHT1Labs, wGninthN2pXHT1Nums,
    2048), (wGninthN2pXHT2Labs, wGninthN2pXHT2Nums, 2048), (wGninthN2pXHT3Labs,
    wGninthN2pXHT3Nums, 2048), (wGninthN2pXHT4Labs, wGninthN2pXHT4Nums, 2048),
    (wGninthN2pXHT5Labs, wGninthN2pXHT5Nums, 2048), (wGninthN2pXHT6Labs, wGninthN2pXHT6Nums,
    2048), (wGninthN2pXHT7Labs, wGninthN2pXHT7Nums, 2048), (wGninthN2pXHT8Labs,
    wGninthN2pXHT8Nums, 2048), (wGninthN2pXHT9Labs, wGninthN2pXHT9Nums, 2048),
    (wGninthN2pXHT10Labs, wGninthN2pXHT10Nums, 2048), (wGninthN2pXHT11Labs, wGninthN2pXHT11Nums,
    2048), (wGninthN2pXHT12Labs, wGninthN2pXHT12Nums, 2048), (wGninthN2pXHT13Labs,
    wGninthN2pXHT13Nums, 2048), (wGninthN2pXHT14Labs, wGninthN2pXHT14Nums, 2048),
    (wGninthN2pXHT15Labs, wGninthN2pXHT15Nums, 2048), (wGninthN2pXHT16Labs, wGninthN2pXHT16Nums,
    2048), (wGninthN2pXHT17Labs, wGninthN2pXHT17Nums, 2048), (wGninthN2pXHT18Labs,
    wGninthN2pXHT18Nums, 2048), (wGninthN2pXHT19Labs, wGninthN2pXHT19Nums, 2048),
    (wGninthN2pXHT20Labs, wGninthN2pXHT20Nums, 2048), (wGninthN2pXHT21Labs, wGninthN2pXHT21Nums,
    2048), (wGninthN2pXHT22Labs, wGninthN2pXHT22Nums, 2048), (wGninthN2pXHT23Labs,
    wGninthN2pXHT23Nums, 2048), (wGninthN2pXHT24Labs, wGninthN2pXHT24Nums, 2048),
    (wGninthN2pXHT25Labs, wGninthN2pXHT25Nums, 2048), (wGninthN2pXHT26Labs, wGninthN2pXHT26Nums,
    2048), (wGninthN2pXHT27Labs, wGninthN2pXHT27Nums, 2048), (wGninthN2pXHT28Labs,
    wGninthN2pXHT28Nums, 2048), (wGninthN2pXHT29Labs, wGninthN2pXHT29Nums, 2048),
    (wGninthN2pXHT30Labs, wGninthN2pXHT30Nums, 144)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGninthN2pX_Wsh : wGninthN2pXW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN2pXGT0Labs, wGninthN2pXGT0Nums, 2048), (wGninthN2pXGT1Labs, wGninthN2pXGT1Nums,
    2048), (wGninthN2pXGT2Labs, wGninthN2pXGT2Nums, 2048), (wGninthN2pXGT3Labs,
    wGninthN2pXGT3Nums, 2048), (wGninthN2pXGT4Labs, wGninthN2pXGT4Nums, 2048),
    (wGninthN2pXGT5Labs, wGninthN2pXGT5Nums, 2048), (wGninthN2pXGT6Labs, wGninthN2pXGT6Nums,
    2048), (wGninthN2pXGT7Labs, wGninthN2pXGT7Nums, 2048), (wGninthN2pXGT8Labs,
    wGninthN2pXGT8Nums, 2048), (wGninthN2pXGT9Labs, wGninthN2pXGT9Nums, 2048),
    (wGninthN2pXGT10Labs, wGninthN2pXGT10Nums, 2048), (wGninthN2pXGT11Labs, wGninthN2pXGT11Nums,
    2048), (wGninthN2pXGT12Labs, wGninthN2pXGT12Nums, 2048), (wGninthN2pXGT13Labs,
    wGninthN2pXGT13Nums, 2048), (wGninthN2pXGT14Labs, wGninthN2pXGT14Nums, 2048),
    (wGninthN2pXGT15Labs, wGninthN2pXGT15Nums, 2048), (wGninthN2pXGT16Labs, wGninthN2pXGT16Nums,
    2048), (wGninthN2pXGT17Labs, wGninthN2pXGT17Nums, 2048), (wGninthN2pXGT18Labs,
    wGninthN2pXGT18Nums, 2048), (wGninthN2pXGT19Labs, wGninthN2pXGT19Nums, 2048),
    (wGninthN2pXGT20Labs, wGninthN2pXGT20Nums, 2048), (wGninthN2pXGT21Labs, wGninthN2pXGT21Nums,
    2048), (wGninthN2pXGT22Labs, wGninthN2pXGT22Nums, 1026)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGninthN2pX_hok : octPackOk 64 wGninthN2pXL = true :=
  OctadDense.octPackOk_of_chk 64 7 true wGninthN2pXL _ _ 4016128 wGninthN2pX_Lsh wGninthN2pX_chk

/-- The octad integer sum. -/
theorem wGninthN2pX_octn : octSumZ 64 true wGninthN2pXL wGninthN2pXW = 4016128 :=
  OctadDense.octSumZ_of_chk 64 7 true wGninthN2pXL wGninthN2pXW _ _ 4016128 wGninthN2pX_Lsh
      wGninthN2pX_Wsh wGninthN2pX_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGninthN2pX_selfchk : OctadDense.selfOctChk 64 [(wGninthN2pXGT0Labs, wGninthN2pXGT0Nums,
    2048), (wGninthN2pXGT1Labs, wGninthN2pXGT1Nums, 2048), (wGninthN2pXGT2Labs,
    wGninthN2pXGT2Nums, 2048), (wGninthN2pXGT3Labs, wGninthN2pXGT3Nums, 2048),
    (wGninthN2pXGT4Labs, wGninthN2pXGT4Nums, 2048), (wGninthN2pXGT5Labs, wGninthN2pXGT5Nums,
    2048), (wGninthN2pXGT6Labs, wGninthN2pXGT6Nums, 2048), (wGninthN2pXGT7Labs,
    wGninthN2pXGT7Nums, 2048), (wGninthN2pXGT8Labs, wGninthN2pXGT8Nums, 2048),
    (wGninthN2pXGT9Labs, wGninthN2pXGT9Nums, 2048), (wGninthN2pXGT10Labs, wGninthN2pXGT10Nums,
    2048), (wGninthN2pXGT11Labs, wGninthN2pXGT11Nums, 2048), (wGninthN2pXGT12Labs,
    wGninthN2pXGT12Nums, 2048), (wGninthN2pXGT13Labs, wGninthN2pXGT13Nums, 2048),
    (wGninthN2pXGT14Labs, wGninthN2pXGT14Nums, 2048), (wGninthN2pXGT15Labs, wGninthN2pXGT15Nums,
    2048), (wGninthN2pXGT16Labs, wGninthN2pXGT16Nums, 2048), (wGninthN2pXGT17Labs,
    wGninthN2pXGT17Nums, 2048), (wGninthN2pXGT18Labs, wGninthN2pXGT18Nums, 2048),
    (wGninthN2pXGT19Labs, wGninthN2pXGT19Nums, 2048), (wGninthN2pXGT20Labs, wGninthN2pXGT20Nums,
    2048), (wGninthN2pXGT21Labs, wGninthN2pXGT21Nums, 2048), (wGninthN2pXGT22Labs,
    wGninthN2pXGT22Nums, 1026)] 502016 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGninthN2pX_hn : wGninthN2pXL.sden * (octSumZ 64 true wGninthN2pXL wGninthN2pXW : ℚ) / 8 =
    wGninthN2pXW.sden * (selfOctP wGninthN2pXW : ℚ) := by
  rw [wGninthN2pX_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGninthN2pXW _ 502016
      wGninthN2pX_Wsh wGninthN2pX_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
