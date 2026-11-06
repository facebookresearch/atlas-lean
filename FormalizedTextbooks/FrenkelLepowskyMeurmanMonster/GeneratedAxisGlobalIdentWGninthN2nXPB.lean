/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN2nXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octads) of the identification Ninth[3]- <-> Tenth[50]+ (record gninth:N2-, e
= -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGninthN2nX_chk : OctadDense.octSumChk 64 7 false [(wGninthN2nXHT0Labs,
    wGninthN2nXHT0Nums, 2048), (wGninthN2nXHT1Labs, wGninthN2nXHT1Nums, 2048),
    (wGninthN2nXHT2Labs, wGninthN2nXHT2Nums, 2048), (wGninthN2nXHT3Labs, wGninthN2nXHT3Nums,
    2048), (wGninthN2nXHT4Labs, wGninthN2nXHT4Nums, 2048), (wGninthN2nXHT5Labs,
    wGninthN2nXHT5Nums, 2048), (wGninthN2nXHT6Labs, wGninthN2nXHT6Nums, 2048),
    (wGninthN2nXHT7Labs, wGninthN2nXHT7Nums, 2048), (wGninthN2nXHT8Labs, wGninthN2nXHT8Nums,
    2048), (wGninthN2nXHT9Labs, wGninthN2nXHT9Nums, 2048), (wGninthN2nXHT10Labs,
    wGninthN2nXHT10Nums, 2048), (wGninthN2nXHT11Labs, wGninthN2nXHT11Nums, 2048),
    (wGninthN2nXHT12Labs, wGninthN2nXHT12Nums, 2048), (wGninthN2nXHT13Labs, wGninthN2nXHT13Nums,
    2048), (wGninthN2nXHT14Labs, wGninthN2nXHT14Nums, 2048), (wGninthN2nXHT15Labs,
    wGninthN2nXHT15Nums, 2048), (wGninthN2nXHT16Labs, wGninthN2nXHT16Nums, 2048),
    (wGninthN2nXHT17Labs, wGninthN2nXHT17Nums, 2048), (wGninthN2nXHT18Labs, wGninthN2nXHT18Nums,
    2048), (wGninthN2nXHT19Labs, wGninthN2nXHT19Nums, 2048), (wGninthN2nXHT20Labs,
    wGninthN2nXHT20Nums, 2048), (wGninthN2nXHT21Labs, wGninthN2nXHT21Nums, 2048),
    (wGninthN2nXHT22Labs, wGninthN2nXHT22Nums, 2048), (wGninthN2nXHT23Labs, wGninthN2nXHT23Nums,
    2048), (wGninthN2nXHT24Labs, wGninthN2nXHT24Nums, 2048), (wGninthN2nXHT25Labs,
    wGninthN2nXHT25Nums, 2048), (wGninthN2nXHT26Labs, wGninthN2nXHT26Nums, 2048),
    (wGninthN2nXHT27Labs, wGninthN2nXHT27Nums, 2048), (wGninthN2nXHT28Labs, wGninthN2nXHT28Nums,
    2048), (wGninthN2nXHT29Labs, wGninthN2nXHT29Nums, 2048), (wGninthN2nXHT30Labs,
    wGninthN2nXHT30Nums, 144)] [(wGninthN2nXGT0Labs, wGninthN2nXGT0Nums, 2048),
    (wGninthN2nXGT1Labs, wGninthN2nXGT1Nums, 2048), (wGninthN2nXGT2Labs, wGninthN2nXGT2Nums,
    2048), (wGninthN2nXGT3Labs, wGninthN2nXGT3Nums, 2048), (wGninthN2nXGT4Labs,
    wGninthN2nXGT4Nums, 2048), (wGninthN2nXGT5Labs, wGninthN2nXGT5Nums, 2048),
    (wGninthN2nXGT6Labs, wGninthN2nXGT6Nums, 2048), (wGninthN2nXGT7Labs, wGninthN2nXGT7Nums,
    2048), (wGninthN2nXGT8Labs, wGninthN2nXGT8Nums, 2048), (wGninthN2nXGT9Labs,
    wGninthN2nXGT9Nums, 2048), (wGninthN2nXGT10Labs, wGninthN2nXGT10Nums, 2048),
    (wGninthN2nXGT11Labs, wGninthN2nXGT11Nums, 2048), (wGninthN2nXGT12Labs, wGninthN2nXGT12Nums,
    2048), (wGninthN2nXGT13Labs, wGninthN2nXGT13Nums, 2048), (wGninthN2nXGT14Labs,
    wGninthN2nXGT14Nums, 2048), (wGninthN2nXGT15Labs, wGninthN2nXGT15Nums, 2048),
    (wGninthN2nXGT16Labs, wGninthN2nXGT16Nums, 2048), (wGninthN2nXGT17Labs, wGninthN2nXGT17Nums,
    2048), (wGninthN2nXGT18Labs, wGninthN2nXGT18Nums, 2048), (wGninthN2nXGT19Labs,
    wGninthN2nXGT19Nums, 2048), (wGninthN2nXGT20Labs, wGninthN2nXGT20Nums, 2048),
    (wGninthN2nXGT21Labs, wGninthN2nXGT21Nums, 2048), (wGninthN2nXGT22Labs, wGninthN2nXGT22Nums,
    1026)] 4016128 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGninthN2nX_Lsh : wGninthN2nXL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN2nXHT0Labs, wGninthN2nXHT0Nums, 2048), (wGninthN2nXHT1Labs, wGninthN2nXHT1Nums,
    2048), (wGninthN2nXHT2Labs, wGninthN2nXHT2Nums, 2048), (wGninthN2nXHT3Labs,
    wGninthN2nXHT3Nums, 2048), (wGninthN2nXHT4Labs, wGninthN2nXHT4Nums, 2048),
    (wGninthN2nXHT5Labs, wGninthN2nXHT5Nums, 2048), (wGninthN2nXHT6Labs, wGninthN2nXHT6Nums,
    2048), (wGninthN2nXHT7Labs, wGninthN2nXHT7Nums, 2048), (wGninthN2nXHT8Labs,
    wGninthN2nXHT8Nums, 2048), (wGninthN2nXHT9Labs, wGninthN2nXHT9Nums, 2048),
    (wGninthN2nXHT10Labs, wGninthN2nXHT10Nums, 2048), (wGninthN2nXHT11Labs, wGninthN2nXHT11Nums,
    2048), (wGninthN2nXHT12Labs, wGninthN2nXHT12Nums, 2048), (wGninthN2nXHT13Labs,
    wGninthN2nXHT13Nums, 2048), (wGninthN2nXHT14Labs, wGninthN2nXHT14Nums, 2048),
    (wGninthN2nXHT15Labs, wGninthN2nXHT15Nums, 2048), (wGninthN2nXHT16Labs, wGninthN2nXHT16Nums,
    2048), (wGninthN2nXHT17Labs, wGninthN2nXHT17Nums, 2048), (wGninthN2nXHT18Labs,
    wGninthN2nXHT18Nums, 2048), (wGninthN2nXHT19Labs, wGninthN2nXHT19Nums, 2048),
    (wGninthN2nXHT20Labs, wGninthN2nXHT20Nums, 2048), (wGninthN2nXHT21Labs, wGninthN2nXHT21Nums,
    2048), (wGninthN2nXHT22Labs, wGninthN2nXHT22Nums, 2048), (wGninthN2nXHT23Labs,
    wGninthN2nXHT23Nums, 2048), (wGninthN2nXHT24Labs, wGninthN2nXHT24Nums, 2048),
    (wGninthN2nXHT25Labs, wGninthN2nXHT25Nums, 2048), (wGninthN2nXHT26Labs, wGninthN2nXHT26Nums,
    2048), (wGninthN2nXHT27Labs, wGninthN2nXHT27Nums, 2048), (wGninthN2nXHT28Labs,
    wGninthN2nXHT28Nums, 2048), (wGninthN2nXHT29Labs, wGninthN2nXHT29Nums, 2048),
    (wGninthN2nXHT30Labs, wGninthN2nXHT30Nums, 144)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGninthN2nX_Wsh : wGninthN2nXW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN2nXGT0Labs, wGninthN2nXGT0Nums, 2048), (wGninthN2nXGT1Labs, wGninthN2nXGT1Nums,
    2048), (wGninthN2nXGT2Labs, wGninthN2nXGT2Nums, 2048), (wGninthN2nXGT3Labs,
    wGninthN2nXGT3Nums, 2048), (wGninthN2nXGT4Labs, wGninthN2nXGT4Nums, 2048),
    (wGninthN2nXGT5Labs, wGninthN2nXGT5Nums, 2048), (wGninthN2nXGT6Labs, wGninthN2nXGT6Nums,
    2048), (wGninthN2nXGT7Labs, wGninthN2nXGT7Nums, 2048), (wGninthN2nXGT8Labs,
    wGninthN2nXGT8Nums, 2048), (wGninthN2nXGT9Labs, wGninthN2nXGT9Nums, 2048),
    (wGninthN2nXGT10Labs, wGninthN2nXGT10Nums, 2048), (wGninthN2nXGT11Labs, wGninthN2nXGT11Nums,
    2048), (wGninthN2nXGT12Labs, wGninthN2nXGT12Nums, 2048), (wGninthN2nXGT13Labs,
    wGninthN2nXGT13Nums, 2048), (wGninthN2nXGT14Labs, wGninthN2nXGT14Nums, 2048),
    (wGninthN2nXGT15Labs, wGninthN2nXGT15Nums, 2048), (wGninthN2nXGT16Labs, wGninthN2nXGT16Nums,
    2048), (wGninthN2nXGT17Labs, wGninthN2nXGT17Nums, 2048), (wGninthN2nXGT18Labs,
    wGninthN2nXGT18Nums, 2048), (wGninthN2nXGT19Labs, wGninthN2nXGT19Nums, 2048),
    (wGninthN2nXGT20Labs, wGninthN2nXGT20Nums, 2048), (wGninthN2nXGT21Labs, wGninthN2nXGT21Nums,
    2048), (wGninthN2nXGT22Labs, wGninthN2nXGT22Nums, 1026)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGninthN2nX_hok : octPackOk 64 wGninthN2nXL = true :=
  OctadDense.octPackOk_of_chk 64 7 false wGninthN2nXL _ _ 4016128 wGninthN2nX_Lsh wGninthN2nX_chk

/-- The octad integer sum. -/
theorem wGninthN2nX_octn : octSumZ 64 false wGninthN2nXL wGninthN2nXW = 4016128 :=
  OctadDense.octSumZ_of_chk 64 7 false wGninthN2nXL wGninthN2nXW _ _ 4016128 wGninthN2nX_Lsh
      wGninthN2nX_Wsh wGninthN2nX_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGninthN2nX_selfchk : OctadDense.selfOctChk 64 [(wGninthN2nXGT0Labs, wGninthN2nXGT0Nums,
    2048), (wGninthN2nXGT1Labs, wGninthN2nXGT1Nums, 2048), (wGninthN2nXGT2Labs,
    wGninthN2nXGT2Nums, 2048), (wGninthN2nXGT3Labs, wGninthN2nXGT3Nums, 2048),
    (wGninthN2nXGT4Labs, wGninthN2nXGT4Nums, 2048), (wGninthN2nXGT5Labs, wGninthN2nXGT5Nums,
    2048), (wGninthN2nXGT6Labs, wGninthN2nXGT6Nums, 2048), (wGninthN2nXGT7Labs,
    wGninthN2nXGT7Nums, 2048), (wGninthN2nXGT8Labs, wGninthN2nXGT8Nums, 2048),
    (wGninthN2nXGT9Labs, wGninthN2nXGT9Nums, 2048), (wGninthN2nXGT10Labs, wGninthN2nXGT10Nums,
    2048), (wGninthN2nXGT11Labs, wGninthN2nXGT11Nums, 2048), (wGninthN2nXGT12Labs,
    wGninthN2nXGT12Nums, 2048), (wGninthN2nXGT13Labs, wGninthN2nXGT13Nums, 2048),
    (wGninthN2nXGT14Labs, wGninthN2nXGT14Nums, 2048), (wGninthN2nXGT15Labs, wGninthN2nXGT15Nums,
    2048), (wGninthN2nXGT16Labs, wGninthN2nXGT16Nums, 2048), (wGninthN2nXGT17Labs,
    wGninthN2nXGT17Nums, 2048), (wGninthN2nXGT18Labs, wGninthN2nXGT18Nums, 2048),
    (wGninthN2nXGT19Labs, wGninthN2nXGT19Nums, 2048), (wGninthN2nXGT20Labs, wGninthN2nXGT20Nums,
    2048), (wGninthN2nXGT21Labs, wGninthN2nXGT21Nums, 2048), (wGninthN2nXGT22Labs,
    wGninthN2nXGT22Nums, 1026)] 502016 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGninthN2nX_hn : wGninthN2nXL.sden * (octSumZ 64 false wGninthN2nXL wGninthN2nXW : ℚ) / 8 =
    wGninthN2nXW.sden * (selfOctP wGninthN2nXW : ℚ) := by
  rw [wGninthN2nX_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGninthN2nXW _ 502016
      wGninthN2nX_Wsh wGninthN2nX_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
