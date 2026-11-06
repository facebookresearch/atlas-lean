/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR81pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (octads) of the identification Root8[16]+ <-> Twelfth[24]+ (record r8f:R81+, e
= 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wR8fR81p_chk : OctadDense.octSumChk 64 6 true [(wR8fR81pHT0Labs, wR8fR81pHT0Nums, 2048),
    (wR8fR81pHT1Labs, wR8fR81pHT1Nums, 2048), (wR8fR81pHT2Labs, wR8fR81pHT2Nums, 2048),
    (wR8fR81pHT3Labs, wR8fR81pHT3Nums, 2048), (wR8fR81pHT4Labs, wR8fR81pHT4Nums, 2048),
    (wR8fR81pHT5Labs, wR8fR81pHT5Nums, 2048), (wR8fR81pHT6Labs, wR8fR81pHT6Nums, 2048),
    (wR8fR81pHT7Labs, wR8fR81pHT7Nums, 2048), (wR8fR81pHT8Labs, wR8fR81pHT8Nums, 2048),
    (wR8fR81pHT9Labs, wR8fR81pHT9Nums, 2048), (wR8fR81pHT10Labs, wR8fR81pHT10Nums, 2048),
    (wR8fR81pHT11Labs, wR8fR81pHT11Nums, 2048), (wR8fR81pHT12Labs, wR8fR81pHT12Nums, 2048),
    (wR8fR81pHT13Labs, wR8fR81pHT13Nums, 2048), (wR8fR81pHT14Labs, wR8fR81pHT14Nums, 2048),
    (wR8fR81pHT15Labs, wR8fR81pHT15Nums, 2048), (wR8fR81pHT16Labs, wR8fR81pHT16Nums, 808)]
    [(wR8fR81pGT0Labs, wR8fR81pGT0Nums, 2048), (wR8fR81pGT1Labs, wR8fR81pGT1Nums, 2048),
    (wR8fR81pGT2Labs, wR8fR81pGT2Nums, 2048), (wR8fR81pGT3Labs, wR8fR81pGT3Nums, 2048),
    (wR8fR81pGT4Labs, wR8fR81pGT4Nums, 2048), (wR8fR81pGT5Labs, wR8fR81pGT5Nums, 2048),
    (wR8fR81pGT6Labs, wR8fR81pGT6Nums, 2048), (wR8fR81pGT7Labs, wR8fR81pGT7Nums, 2048),
    (wR8fR81pGT8Labs, wR8fR81pGT8Nums, 2048), (wR8fR81pGT9Labs, wR8fR81pGT9Nums, 2048),
    (wR8fR81pGT10Labs, wR8fR81pGT10Nums, 2048), (wR8fR81pGT11Labs, wR8fR81pGT11Nums, 2048),
    (wR8fR81pGT12Labs, wR8fR81pGT12Nums, 2048), (wR8fR81pGT13Labs, wR8fR81pGT13Nums, 2048),
    (wR8fR81pGT14Labs, wR8fR81pGT14Nums, 2048), (wR8fR81pGT15Labs, wR8fR81pGT15Nums, 2048),
    (wR8fR81pGT16Labs, wR8fR81pGT16Nums, 2048), (wR8fR81pGT17Labs, wR8fR81pGT17Nums, 2048),
    (wR8fR81pGT18Labs, wR8fR81pGT18Nums, 2048), (wR8fR81pGT19Labs, wR8fR81pGT19Nums, 2048),
    (wR8fR81pGT20Labs, wR8fR81pGT20Nums, 2048), (wR8fR81pGT21Labs, wR8fR81pGT21Nums, 2048),
    (wR8fR81pGT22Labs, wR8fR81pGT22Nums, 1704)] 4047872 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wR8fR81p_Lsh : wR8fR81pL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR81pHT0Labs, wR8fR81pHT0Nums, 2048), (wR8fR81pHT1Labs, wR8fR81pHT1Nums, 2048),
    (wR8fR81pHT2Labs, wR8fR81pHT2Nums, 2048), (wR8fR81pHT3Labs, wR8fR81pHT3Nums, 2048),
    (wR8fR81pHT4Labs, wR8fR81pHT4Nums, 2048), (wR8fR81pHT5Labs, wR8fR81pHT5Nums, 2048),
    (wR8fR81pHT6Labs, wR8fR81pHT6Nums, 2048), (wR8fR81pHT7Labs, wR8fR81pHT7Nums, 2048),
    (wR8fR81pHT8Labs, wR8fR81pHT8Nums, 2048), (wR8fR81pHT9Labs, wR8fR81pHT9Nums, 2048),
    (wR8fR81pHT10Labs, wR8fR81pHT10Nums, 2048), (wR8fR81pHT11Labs, wR8fR81pHT11Nums, 2048),
    (wR8fR81pHT12Labs, wR8fR81pHT12Nums, 2048), (wR8fR81pHT13Labs, wR8fR81pHT13Nums, 2048),
    (wR8fR81pHT14Labs, wR8fR81pHT14Nums, 2048), (wR8fR81pHT15Labs, wR8fR81pHT15Nums, 2048),
    (wR8fR81pHT16Labs, wR8fR81pHT16Nums, 808)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wR8fR81p_Wsh : wR8fR81pW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR81pGT0Labs, wR8fR81pGT0Nums, 2048), (wR8fR81pGT1Labs, wR8fR81pGT1Nums, 2048),
    (wR8fR81pGT2Labs, wR8fR81pGT2Nums, 2048), (wR8fR81pGT3Labs, wR8fR81pGT3Nums, 2048),
    (wR8fR81pGT4Labs, wR8fR81pGT4Nums, 2048), (wR8fR81pGT5Labs, wR8fR81pGT5Nums, 2048),
    (wR8fR81pGT6Labs, wR8fR81pGT6Nums, 2048), (wR8fR81pGT7Labs, wR8fR81pGT7Nums, 2048),
    (wR8fR81pGT8Labs, wR8fR81pGT8Nums, 2048), (wR8fR81pGT9Labs, wR8fR81pGT9Nums, 2048),
    (wR8fR81pGT10Labs, wR8fR81pGT10Nums, 2048), (wR8fR81pGT11Labs, wR8fR81pGT11Nums, 2048),
    (wR8fR81pGT12Labs, wR8fR81pGT12Nums, 2048), (wR8fR81pGT13Labs, wR8fR81pGT13Nums, 2048),
    (wR8fR81pGT14Labs, wR8fR81pGT14Nums, 2048), (wR8fR81pGT15Labs, wR8fR81pGT15Nums, 2048),
    (wR8fR81pGT16Labs, wR8fR81pGT16Nums, 2048), (wR8fR81pGT17Labs, wR8fR81pGT17Nums, 2048),
    (wR8fR81pGT18Labs, wR8fR81pGT18Nums, 2048), (wR8fR81pGT19Labs, wR8fR81pGT19Nums, 2048),
    (wR8fR81pGT20Labs, wR8fR81pGT20Nums, 2048), (wR8fR81pGT21Labs, wR8fR81pGT21Nums, 2048),
    (wR8fR81pGT22Labs, wR8fR81pGT22Nums, 1704)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wR8fR81p_hok : octPackOk 64 wR8fR81pL = true :=
  OctadDense.octPackOk_of_chk 64 6 true wR8fR81pL _ _ 4047872 wR8fR81p_Lsh wR8fR81p_chk

/-- The octad integer sum. -/
theorem wR8fR81p_octn : octSumZ 64 true wR8fR81pL wR8fR81pW = 4047872 :=
  OctadDense.octSumZ_of_chk 64 6 true wR8fR81pL wR8fR81pW _ _ 4047872 wR8fR81p_Lsh wR8fR81p_Wsh
      wR8fR81p_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wR8fR81p_selfchk : OctadDense.selfOctChk 64 [(wR8fR81pGT0Labs, wR8fR81pGT0Nums, 2048),
    (wR8fR81pGT1Labs, wR8fR81pGT1Nums, 2048), (wR8fR81pGT2Labs, wR8fR81pGT2Nums, 2048),
    (wR8fR81pGT3Labs, wR8fR81pGT3Nums, 2048), (wR8fR81pGT4Labs, wR8fR81pGT4Nums, 2048),
    (wR8fR81pGT5Labs, wR8fR81pGT5Nums, 2048), (wR8fR81pGT6Labs, wR8fR81pGT6Nums, 2048),
    (wR8fR81pGT7Labs, wR8fR81pGT7Nums, 2048), (wR8fR81pGT8Labs, wR8fR81pGT8Nums, 2048),
    (wR8fR81pGT9Labs, wR8fR81pGT9Nums, 2048), (wR8fR81pGT10Labs, wR8fR81pGT10Nums, 2048),
    (wR8fR81pGT11Labs, wR8fR81pGT11Nums, 2048), (wR8fR81pGT12Labs, wR8fR81pGT12Nums, 2048),
    (wR8fR81pGT13Labs, wR8fR81pGT13Nums, 2048), (wR8fR81pGT14Labs, wR8fR81pGT14Nums, 2048),
    (wR8fR81pGT15Labs, wR8fR81pGT15Nums, 2048), (wR8fR81pGT16Labs, wR8fR81pGT16Nums, 2048),
    (wR8fR81pGT17Labs, wR8fR81pGT17Nums, 2048), (wR8fR81pGT18Labs, wR8fR81pGT18Nums, 2048),
    (wR8fR81pGT19Labs, wR8fR81pGT19Nums, 2048), (wR8fR81pGT20Labs, wR8fR81pGT20Nums, 2048),
    (wR8fR81pGT21Labs, wR8fR81pGT21Nums, 2048), (wR8fR81pGT22Labs, wR8fR81pGT22Nums, 1704)] 505984
    = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wR8fR81p_hn : wR8fR81pL.sden * (octSumZ 64 true wR8fR81pL wR8fR81pW : ℚ) / 8 =
    wR8fR81pW.sden * (selfOctP wR8fR81pW : ℚ) := by
  rw [wR8fR81p_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wR8fR81pW _ 505984 wR8fR81p_Wsh
      wR8fR81p_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
