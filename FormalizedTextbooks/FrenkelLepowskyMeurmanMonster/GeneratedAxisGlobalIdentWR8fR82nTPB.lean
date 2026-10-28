/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR82nTChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octads) of the identification Root8[2]- <-> Tenth[38]+ (record r8f:R82-, e =
-1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wR8fR82nT_chk : OctadDense.octSumChk 64 7 false [(wR8fR82nTHT0Labs, wR8fR82nTHT0Nums,
    2048), (wR8fR82nTHT1Labs, wR8fR82nTHT1Nums, 2048), (wR8fR82nTHT2Labs, wR8fR82nTHT2Nums, 2048),
    (wR8fR82nTHT3Labs, wR8fR82nTHT3Nums, 2048), (wR8fR82nTHT4Labs, wR8fR82nTHT4Nums, 2048),
    (wR8fR82nTHT5Labs, wR8fR82nTHT5Nums, 2048), (wR8fR82nTHT6Labs, wR8fR82nTHT6Nums, 2048),
    (wR8fR82nTHT7Labs, wR8fR82nTHT7Nums, 2048), (wR8fR82nTHT8Labs, wR8fR82nTHT8Nums, 2048),
    (wR8fR82nTHT9Labs, wR8fR82nTHT9Nums, 2048), (wR8fR82nTHT10Labs, wR8fR82nTHT10Nums, 2048),
    (wR8fR82nTHT11Labs, wR8fR82nTHT11Nums, 2048), (wR8fR82nTHT12Labs, wR8fR82nTHT12Nums, 2048),
    (wR8fR82nTHT13Labs, wR8fR82nTHT13Nums, 2048), (wR8fR82nTHT14Labs, wR8fR82nTHT14Nums, 2048),
    (wR8fR82nTHT15Labs, wR8fR82nTHT15Nums, 2048), (wR8fR82nTHT16Labs, wR8fR82nTHT16Nums, 808)]
    [(wR8fR82nTGT0Labs, wR8fR82nTGT0Nums, 2048), (wR8fR82nTGT1Labs, wR8fR82nTGT1Nums, 2048),
    (wR8fR82nTGT2Labs, wR8fR82nTGT2Nums, 2048), (wR8fR82nTGT3Labs, wR8fR82nTGT3Nums, 2048),
    (wR8fR82nTGT4Labs, wR8fR82nTGT4Nums, 2048), (wR8fR82nTGT5Labs, wR8fR82nTGT5Nums, 2048),
    (wR8fR82nTGT6Labs, wR8fR82nTGT6Nums, 2048), (wR8fR82nTGT7Labs, wR8fR82nTGT7Nums, 2048),
    (wR8fR82nTGT8Labs, wR8fR82nTGT8Nums, 2048), (wR8fR82nTGT9Labs, wR8fR82nTGT9Nums, 2048),
    (wR8fR82nTGT10Labs, wR8fR82nTGT10Nums, 2048), (wR8fR82nTGT11Labs, wR8fR82nTGT11Nums, 2048),
    (wR8fR82nTGT12Labs, wR8fR82nTGT12Nums, 2048), (wR8fR82nTGT13Labs, wR8fR82nTGT13Nums, 2048),
    (wR8fR82nTGT14Labs, wR8fR82nTGT14Nums, 2048), (wR8fR82nTGT15Labs, wR8fR82nTGT15Nums, 2048),
    (wR8fR82nTGT16Labs, wR8fR82nTGT16Nums, 2048), (wR8fR82nTGT17Labs, wR8fR82nTGT17Nums, 2048),
    (wR8fR82nTGT18Labs, wR8fR82nTGT18Nums, 2048), (wR8fR82nTGT19Labs, wR8fR82nTGT19Nums, 2048),
    (wR8fR82nTGT20Labs, wR8fR82nTGT20Nums, 2048), (wR8fR82nTGT21Labs, wR8fR82nTGT21Nums, 2048),
    (wR8fR82nTGT22Labs, wR8fR82nTGT22Nums, 1026)] 4054528 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wR8fR82nT_Lsh : wR8fR82nTL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR82nTHT0Labs, wR8fR82nTHT0Nums, 2048), (wR8fR82nTHT1Labs, wR8fR82nTHT1Nums, 2048),
    (wR8fR82nTHT2Labs, wR8fR82nTHT2Nums, 2048), (wR8fR82nTHT3Labs, wR8fR82nTHT3Nums, 2048),
    (wR8fR82nTHT4Labs, wR8fR82nTHT4Nums, 2048), (wR8fR82nTHT5Labs, wR8fR82nTHT5Nums, 2048),
    (wR8fR82nTHT6Labs, wR8fR82nTHT6Nums, 2048), (wR8fR82nTHT7Labs, wR8fR82nTHT7Nums, 2048),
    (wR8fR82nTHT8Labs, wR8fR82nTHT8Nums, 2048), (wR8fR82nTHT9Labs, wR8fR82nTHT9Nums, 2048),
    (wR8fR82nTHT10Labs, wR8fR82nTHT10Nums, 2048), (wR8fR82nTHT11Labs, wR8fR82nTHT11Nums, 2048),
    (wR8fR82nTHT12Labs, wR8fR82nTHT12Nums, 2048), (wR8fR82nTHT13Labs, wR8fR82nTHT13Nums, 2048),
    (wR8fR82nTHT14Labs, wR8fR82nTHT14Nums, 2048), (wR8fR82nTHT15Labs, wR8fR82nTHT15Nums, 2048),
    (wR8fR82nTHT16Labs, wR8fR82nTHT16Nums, 808)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wR8fR82nT_Wsh : wR8fR82nTW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR82nTGT0Labs, wR8fR82nTGT0Nums, 2048), (wR8fR82nTGT1Labs, wR8fR82nTGT1Nums, 2048),
    (wR8fR82nTGT2Labs, wR8fR82nTGT2Nums, 2048), (wR8fR82nTGT3Labs, wR8fR82nTGT3Nums, 2048),
    (wR8fR82nTGT4Labs, wR8fR82nTGT4Nums, 2048), (wR8fR82nTGT5Labs, wR8fR82nTGT5Nums, 2048),
    (wR8fR82nTGT6Labs, wR8fR82nTGT6Nums, 2048), (wR8fR82nTGT7Labs, wR8fR82nTGT7Nums, 2048),
    (wR8fR82nTGT8Labs, wR8fR82nTGT8Nums, 2048), (wR8fR82nTGT9Labs, wR8fR82nTGT9Nums, 2048),
    (wR8fR82nTGT10Labs, wR8fR82nTGT10Nums, 2048), (wR8fR82nTGT11Labs, wR8fR82nTGT11Nums, 2048),
    (wR8fR82nTGT12Labs, wR8fR82nTGT12Nums, 2048), (wR8fR82nTGT13Labs, wR8fR82nTGT13Nums, 2048),
    (wR8fR82nTGT14Labs, wR8fR82nTGT14Nums, 2048), (wR8fR82nTGT15Labs, wR8fR82nTGT15Nums, 2048),
    (wR8fR82nTGT16Labs, wR8fR82nTGT16Nums, 2048), (wR8fR82nTGT17Labs, wR8fR82nTGT17Nums, 2048),
    (wR8fR82nTGT18Labs, wR8fR82nTGT18Nums, 2048), (wR8fR82nTGT19Labs, wR8fR82nTGT19Nums, 2048),
    (wR8fR82nTGT20Labs, wR8fR82nTGT20Nums, 2048), (wR8fR82nTGT21Labs, wR8fR82nTGT21Nums, 2048),
    (wR8fR82nTGT22Labs, wR8fR82nTGT22Nums, 1026)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wR8fR82nT_hok : octPackOk 64 wR8fR82nTL = true :=
  OctadDense.octPackOk_of_chk 64 7 false wR8fR82nTL _ _ 4054528 wR8fR82nT_Lsh wR8fR82nT_chk

/-- The octad integer sum. -/
theorem wR8fR82nT_octn : octSumZ 64 false wR8fR82nTL wR8fR82nTW = 4054528 :=
  OctadDense.octSumZ_of_chk 64 7 false wR8fR82nTL wR8fR82nTW _ _ 4054528 wR8fR82nT_Lsh
      wR8fR82nT_Wsh wR8fR82nT_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wR8fR82nT_selfchk : OctadDense.selfOctChk 64 [(wR8fR82nTGT0Labs, wR8fR82nTGT0Nums, 2048),
    (wR8fR82nTGT1Labs, wR8fR82nTGT1Nums, 2048), (wR8fR82nTGT2Labs, wR8fR82nTGT2Nums, 2048),
    (wR8fR82nTGT3Labs, wR8fR82nTGT3Nums, 2048), (wR8fR82nTGT4Labs, wR8fR82nTGT4Nums, 2048),
    (wR8fR82nTGT5Labs, wR8fR82nTGT5Nums, 2048), (wR8fR82nTGT6Labs, wR8fR82nTGT6Nums, 2048),
    (wR8fR82nTGT7Labs, wR8fR82nTGT7Nums, 2048), (wR8fR82nTGT8Labs, wR8fR82nTGT8Nums, 2048),
    (wR8fR82nTGT9Labs, wR8fR82nTGT9Nums, 2048), (wR8fR82nTGT10Labs, wR8fR82nTGT10Nums, 2048),
    (wR8fR82nTGT11Labs, wR8fR82nTGT11Nums, 2048), (wR8fR82nTGT12Labs, wR8fR82nTGT12Nums, 2048),
    (wR8fR82nTGT13Labs, wR8fR82nTGT13Nums, 2048), (wR8fR82nTGT14Labs, wR8fR82nTGT14Nums, 2048),
    (wR8fR82nTGT15Labs, wR8fR82nTGT15Nums, 2048), (wR8fR82nTGT16Labs, wR8fR82nTGT16Nums, 2048),
    (wR8fR82nTGT17Labs, wR8fR82nTGT17Nums, 2048), (wR8fR82nTGT18Labs, wR8fR82nTGT18Nums, 2048),
    (wR8fR82nTGT19Labs, wR8fR82nTGT19Nums, 2048), (wR8fR82nTGT20Labs, wR8fR82nTGT20Nums, 2048),
    (wR8fR82nTGT21Labs, wR8fR82nTGT21Nums, 2048), (wR8fR82nTGT22Labs, wR8fR82nTGT22Nums, 1026)]
    506816 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wR8fR82nT_hn : wR8fR82nTL.sden * (octSumZ 64 false wR8fR82nTL wR8fR82nTW : ℚ) / 8 =
    wR8fR82nTW.sden * (selfOctP wR8fR82nTW : ℚ) := by
  rw [wR8fR82nT_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wR8fR82nTW _ 506816 wR8fR82nT_Wsh
      wR8fR82nT_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
