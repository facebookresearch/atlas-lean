/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN1nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octads) of the identification Ninth[1]- <-> Tenth[33]+ (record gninth:N1-, e
= -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGninthN1n_chk : OctadDense.octSumChk 64 6 false [(wGninthN1nHT0Labs, wGninthN1nHT0Nums,
    2048), (wGninthN1nHT1Labs, wGninthN1nHT1Nums, 2048), (wGninthN1nHT2Labs, wGninthN1nHT2Nums,
    2048), (wGninthN1nHT3Labs, wGninthN1nHT3Nums, 2048), (wGninthN1nHT4Labs, wGninthN1nHT4Nums,
    2048), (wGninthN1nHT5Labs, wGninthN1nHT5Nums, 2048), (wGninthN1nHT6Labs, wGninthN1nHT6Nums,
    2048), (wGninthN1nHT7Labs, wGninthN1nHT7Nums, 2048), (wGninthN1nHT8Labs, wGninthN1nHT8Nums,
    2048), (wGninthN1nHT9Labs, wGninthN1nHT9Nums, 2048), (wGninthN1nHT10Labs, wGninthN1nHT10Nums,
    2048), (wGninthN1nHT11Labs, wGninthN1nHT11Nums, 2048), (wGninthN1nHT12Labs,
    wGninthN1nHT12Nums, 2048), (wGninthN1nHT13Labs, wGninthN1nHT13Nums, 2048),
    (wGninthN1nHT14Labs, wGninthN1nHT14Nums, 2048), (wGninthN1nHT15Labs, wGninthN1nHT15Nums,
    2048), (wGninthN1nHT16Labs, wGninthN1nHT16Nums, 2048), (wGninthN1nHT17Labs,
    wGninthN1nHT17Nums, 2048), (wGninthN1nHT18Labs, wGninthN1nHT18Nums, 2048),
    (wGninthN1nHT19Labs, wGninthN1nHT19Nums, 2048), (wGninthN1nHT20Labs, wGninthN1nHT20Nums,
    2048), (wGninthN1nHT21Labs, wGninthN1nHT21Nums, 2048), (wGninthN1nHT22Labs,
    wGninthN1nHT22Nums, 2048), (wGninthN1nHT23Labs, wGninthN1nHT23Nums, 2048),
    (wGninthN1nHT24Labs, wGninthN1nHT24Nums, 2048), (wGninthN1nHT25Labs, wGninthN1nHT25Nums,
    2048), (wGninthN1nHT26Labs, wGninthN1nHT26Nums, 2048), (wGninthN1nHT27Labs,
    wGninthN1nHT27Nums, 2048), (wGninthN1nHT28Labs, wGninthN1nHT28Nums, 2048),
    (wGninthN1nHT29Labs, wGninthN1nHT29Nums, 2048), (wGninthN1nHT30Labs, wGninthN1nHT30Nums, 144)]
    [(wGninthN1nGT0Labs, wGninthN1nGT0Nums, 2048), (wGninthN1nGT1Labs, wGninthN1nGT1Nums, 2048),
    (wGninthN1nGT2Labs, wGninthN1nGT2Nums, 2048), (wGninthN1nGT3Labs, wGninthN1nGT3Nums, 2048),
    (wGninthN1nGT4Labs, wGninthN1nGT4Nums, 2048), (wGninthN1nGT5Labs, wGninthN1nGT5Nums, 2048),
    (wGninthN1nGT6Labs, wGninthN1nGT6Nums, 2048), (wGninthN1nGT7Labs, wGninthN1nGT7Nums, 2048),
    (wGninthN1nGT8Labs, wGninthN1nGT8Nums, 2048), (wGninthN1nGT9Labs, wGninthN1nGT9Nums, 2048),
    (wGninthN1nGT10Labs, wGninthN1nGT10Nums, 2048), (wGninthN1nGT11Labs, wGninthN1nGT11Nums,
    2048), (wGninthN1nGT12Labs, wGninthN1nGT12Nums, 2048), (wGninthN1nGT13Labs,
    wGninthN1nGT13Nums, 2048), (wGninthN1nGT14Labs, wGninthN1nGT14Nums, 2048),
    (wGninthN1nGT15Labs, wGninthN1nGT15Nums, 2048), (wGninthN1nGT16Labs, wGninthN1nGT16Nums,
    2048), (wGninthN1nGT17Labs, wGninthN1nGT17Nums, 2048), (wGninthN1nGT18Labs,
    wGninthN1nGT18Nums, 2048), (wGninthN1nGT19Labs, wGninthN1nGT19Nums, 2048),
    (wGninthN1nGT20Labs, wGninthN1nGT20Nums, 2048), (wGninthN1nGT21Labs, wGninthN1nGT21Nums,
    2048), (wGninthN1nGT22Labs, wGninthN1nGT22Nums, 1026)] 4034048 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGninthN1n_Lsh : wGninthN1nL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN1nHT0Labs, wGninthN1nHT0Nums, 2048), (wGninthN1nHT1Labs, wGninthN1nHT1Nums, 2048),
    (wGninthN1nHT2Labs, wGninthN1nHT2Nums, 2048), (wGninthN1nHT3Labs, wGninthN1nHT3Nums, 2048),
    (wGninthN1nHT4Labs, wGninthN1nHT4Nums, 2048), (wGninthN1nHT5Labs, wGninthN1nHT5Nums, 2048),
    (wGninthN1nHT6Labs, wGninthN1nHT6Nums, 2048), (wGninthN1nHT7Labs, wGninthN1nHT7Nums, 2048),
    (wGninthN1nHT8Labs, wGninthN1nHT8Nums, 2048), (wGninthN1nHT9Labs, wGninthN1nHT9Nums, 2048),
    (wGninthN1nHT10Labs, wGninthN1nHT10Nums, 2048), (wGninthN1nHT11Labs, wGninthN1nHT11Nums,
    2048), (wGninthN1nHT12Labs, wGninthN1nHT12Nums, 2048), (wGninthN1nHT13Labs,
    wGninthN1nHT13Nums, 2048), (wGninthN1nHT14Labs, wGninthN1nHT14Nums, 2048),
    (wGninthN1nHT15Labs, wGninthN1nHT15Nums, 2048), (wGninthN1nHT16Labs, wGninthN1nHT16Nums,
    2048), (wGninthN1nHT17Labs, wGninthN1nHT17Nums, 2048), (wGninthN1nHT18Labs,
    wGninthN1nHT18Nums, 2048), (wGninthN1nHT19Labs, wGninthN1nHT19Nums, 2048),
    (wGninthN1nHT20Labs, wGninthN1nHT20Nums, 2048), (wGninthN1nHT21Labs, wGninthN1nHT21Nums,
    2048), (wGninthN1nHT22Labs, wGninthN1nHT22Nums, 2048), (wGninthN1nHT23Labs,
    wGninthN1nHT23Nums, 2048), (wGninthN1nHT24Labs, wGninthN1nHT24Nums, 2048),
    (wGninthN1nHT25Labs, wGninthN1nHT25Nums, 2048), (wGninthN1nHT26Labs, wGninthN1nHT26Nums,
    2048), (wGninthN1nHT27Labs, wGninthN1nHT27Nums, 2048), (wGninthN1nHT28Labs,
    wGninthN1nHT28Nums, 2048), (wGninthN1nHT29Labs, wGninthN1nHT29Nums, 2048),
    (wGninthN1nHT30Labs, wGninthN1nHT30Nums, 144)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGninthN1n_Wsh : wGninthN1nW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN1nGT0Labs, wGninthN1nGT0Nums, 2048), (wGninthN1nGT1Labs, wGninthN1nGT1Nums, 2048),
    (wGninthN1nGT2Labs, wGninthN1nGT2Nums, 2048), (wGninthN1nGT3Labs, wGninthN1nGT3Nums, 2048),
    (wGninthN1nGT4Labs, wGninthN1nGT4Nums, 2048), (wGninthN1nGT5Labs, wGninthN1nGT5Nums, 2048),
    (wGninthN1nGT6Labs, wGninthN1nGT6Nums, 2048), (wGninthN1nGT7Labs, wGninthN1nGT7Nums, 2048),
    (wGninthN1nGT8Labs, wGninthN1nGT8Nums, 2048), (wGninthN1nGT9Labs, wGninthN1nGT9Nums, 2048),
    (wGninthN1nGT10Labs, wGninthN1nGT10Nums, 2048), (wGninthN1nGT11Labs, wGninthN1nGT11Nums,
    2048), (wGninthN1nGT12Labs, wGninthN1nGT12Nums, 2048), (wGninthN1nGT13Labs,
    wGninthN1nGT13Nums, 2048), (wGninthN1nGT14Labs, wGninthN1nGT14Nums, 2048),
    (wGninthN1nGT15Labs, wGninthN1nGT15Nums, 2048), (wGninthN1nGT16Labs, wGninthN1nGT16Nums,
    2048), (wGninthN1nGT17Labs, wGninthN1nGT17Nums, 2048), (wGninthN1nGT18Labs,
    wGninthN1nGT18Nums, 2048), (wGninthN1nGT19Labs, wGninthN1nGT19Nums, 2048),
    (wGninthN1nGT20Labs, wGninthN1nGT20Nums, 2048), (wGninthN1nGT21Labs, wGninthN1nGT21Nums,
    2048), (wGninthN1nGT22Labs, wGninthN1nGT22Nums, 1026)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGninthN1n_hok : octPackOk 64 wGninthN1nL = true :=
  OctadDense.octPackOk_of_chk 64 6 false wGninthN1nL _ _ 4034048 wGninthN1n_Lsh wGninthN1n_chk

/-- The octad integer sum. -/
theorem wGninthN1n_octn : octSumZ 64 false wGninthN1nL wGninthN1nW = 4034048 :=
  OctadDense.octSumZ_of_chk 64 6 false wGninthN1nL wGninthN1nW _ _ 4034048 wGninthN1n_Lsh
      wGninthN1n_Wsh wGninthN1n_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGninthN1n_selfchk : OctadDense.selfOctChk 64 [(wGninthN1nGT0Labs, wGninthN1nGT0Nums,
    2048), (wGninthN1nGT1Labs, wGninthN1nGT1Nums, 2048), (wGninthN1nGT2Labs, wGninthN1nGT2Nums,
    2048), (wGninthN1nGT3Labs, wGninthN1nGT3Nums, 2048), (wGninthN1nGT4Labs, wGninthN1nGT4Nums,
    2048), (wGninthN1nGT5Labs, wGninthN1nGT5Nums, 2048), (wGninthN1nGT6Labs, wGninthN1nGT6Nums,
    2048), (wGninthN1nGT7Labs, wGninthN1nGT7Nums, 2048), (wGninthN1nGT8Labs, wGninthN1nGT8Nums,
    2048), (wGninthN1nGT9Labs, wGninthN1nGT9Nums, 2048), (wGninthN1nGT10Labs, wGninthN1nGT10Nums,
    2048), (wGninthN1nGT11Labs, wGninthN1nGT11Nums, 2048), (wGninthN1nGT12Labs,
    wGninthN1nGT12Nums, 2048), (wGninthN1nGT13Labs, wGninthN1nGT13Nums, 2048),
    (wGninthN1nGT14Labs, wGninthN1nGT14Nums, 2048), (wGninthN1nGT15Labs, wGninthN1nGT15Nums,
    2048), (wGninthN1nGT16Labs, wGninthN1nGT16Nums, 2048), (wGninthN1nGT17Labs,
    wGninthN1nGT17Nums, 2048), (wGninthN1nGT18Labs, wGninthN1nGT18Nums, 2048),
    (wGninthN1nGT19Labs, wGninthN1nGT19Nums, 2048), (wGninthN1nGT20Labs, wGninthN1nGT20Nums,
    2048), (wGninthN1nGT21Labs, wGninthN1nGT21Nums, 2048), (wGninthN1nGT22Labs,
    wGninthN1nGT22Nums, 1026)] 504256 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGninthN1n_hn : wGninthN1nL.sden * (octSumZ 64 false wGninthN1nL wGninthN1nW : ℚ) / 8 =
    wGninthN1nW.sden * (selfOctP wGninthN1nW : ℚ) := by
  rw [wGninthN1n_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGninthN1nW _ 504256
      wGninthN1n_Wsh wGninthN1n_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
