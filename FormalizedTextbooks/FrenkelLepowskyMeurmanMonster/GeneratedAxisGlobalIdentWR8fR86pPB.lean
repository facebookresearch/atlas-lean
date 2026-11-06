/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (octads) of the identification Root8[12]+ <-> Twelfth[34]- (record r8f:R86+, e
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
theorem wR8fR86p_chk : OctadDense.octSumChk 64 6 true [(wR8fR86pHT0Labs, wR8fR86pHT0Nums, 2048),
    (wR8fR86pHT1Labs, wR8fR86pHT1Nums, 2048), (wR8fR86pHT2Labs, wR8fR86pHT2Nums, 2048),
    (wR8fR86pHT3Labs, wR8fR86pHT3Nums, 2048), (wR8fR86pHT4Labs, wR8fR86pHT4Nums, 2048),
    (wR8fR86pHT5Labs, wR8fR86pHT5Nums, 2048), (wR8fR86pHT6Labs, wR8fR86pHT6Nums, 2048),
    (wR8fR86pHT7Labs, wR8fR86pHT7Nums, 2048), (wR8fR86pHT8Labs, wR8fR86pHT8Nums, 2048),
    (wR8fR86pHT9Labs, wR8fR86pHT9Nums, 2048), (wR8fR86pHT10Labs, wR8fR86pHT10Nums, 2048),
    (wR8fR86pHT11Labs, wR8fR86pHT11Nums, 2048), (wR8fR86pHT12Labs, wR8fR86pHT12Nums, 2048),
    (wR8fR86pHT13Labs, wR8fR86pHT13Nums, 2048), (wR8fR86pHT14Labs, wR8fR86pHT14Nums, 2048),
    (wR8fR86pHT15Labs, wR8fR86pHT15Nums, 2048), (wR8fR86pHT16Labs, wR8fR86pHT16Nums, 808)]
    [(wR8fR86pGT0Labs, wR8fR86pGT0Nums, 2048), (wR8fR86pGT1Labs, wR8fR86pGT1Nums, 2048),
    (wR8fR86pGT2Labs, wR8fR86pGT2Nums, 2048), (wR8fR86pGT3Labs, wR8fR86pGT3Nums, 2048),
    (wR8fR86pGT4Labs, wR8fR86pGT4Nums, 2048), (wR8fR86pGT5Labs, wR8fR86pGT5Nums, 2048),
    (wR8fR86pGT6Labs, wR8fR86pGT6Nums, 2048), (wR8fR86pGT7Labs, wR8fR86pGT7Nums, 2048),
    (wR8fR86pGT8Labs, wR8fR86pGT8Nums, 2048), (wR8fR86pGT9Labs, wR8fR86pGT9Nums, 2048),
    (wR8fR86pGT10Labs, wR8fR86pGT10Nums, 2048), (wR8fR86pGT11Labs, wR8fR86pGT11Nums, 2048),
    (wR8fR86pGT12Labs, wR8fR86pGT12Nums, 2048), (wR8fR86pGT13Labs, wR8fR86pGT13Nums, 2048),
    (wR8fR86pGT14Labs, wR8fR86pGT14Nums, 2048), (wR8fR86pGT15Labs, wR8fR86pGT15Nums, 2048),
    (wR8fR86pGT16Labs, wR8fR86pGT16Nums, 2048), (wR8fR86pGT17Labs, wR8fR86pGT17Nums, 2048),
    (wR8fR86pGT18Labs, wR8fR86pGT18Nums, 2048), (wR8fR86pGT19Labs, wR8fR86pGT19Nums, 2048),
    (wR8fR86pGT20Labs, wR8fR86pGT20Nums, 2048), (wR8fR86pGT21Labs, wR8fR86pGT21Nums, 2048),
    (wR8fR86pGT22Labs, wR8fR86pGT22Nums, 1704)] 4048896 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wR8fR86p_Lsh : wR8fR86pL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR86pHT0Labs, wR8fR86pHT0Nums, 2048), (wR8fR86pHT1Labs, wR8fR86pHT1Nums, 2048),
    (wR8fR86pHT2Labs, wR8fR86pHT2Nums, 2048), (wR8fR86pHT3Labs, wR8fR86pHT3Nums, 2048),
    (wR8fR86pHT4Labs, wR8fR86pHT4Nums, 2048), (wR8fR86pHT5Labs, wR8fR86pHT5Nums, 2048),
    (wR8fR86pHT6Labs, wR8fR86pHT6Nums, 2048), (wR8fR86pHT7Labs, wR8fR86pHT7Nums, 2048),
    (wR8fR86pHT8Labs, wR8fR86pHT8Nums, 2048), (wR8fR86pHT9Labs, wR8fR86pHT9Nums, 2048),
    (wR8fR86pHT10Labs, wR8fR86pHT10Nums, 2048), (wR8fR86pHT11Labs, wR8fR86pHT11Nums, 2048),
    (wR8fR86pHT12Labs, wR8fR86pHT12Nums, 2048), (wR8fR86pHT13Labs, wR8fR86pHT13Nums, 2048),
    (wR8fR86pHT14Labs, wR8fR86pHT14Nums, 2048), (wR8fR86pHT15Labs, wR8fR86pHT15Nums, 2048),
    (wR8fR86pHT16Labs, wR8fR86pHT16Nums, 808)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wR8fR86p_Wsh : wR8fR86pW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR86pGT0Labs, wR8fR86pGT0Nums, 2048), (wR8fR86pGT1Labs, wR8fR86pGT1Nums, 2048),
    (wR8fR86pGT2Labs, wR8fR86pGT2Nums, 2048), (wR8fR86pGT3Labs, wR8fR86pGT3Nums, 2048),
    (wR8fR86pGT4Labs, wR8fR86pGT4Nums, 2048), (wR8fR86pGT5Labs, wR8fR86pGT5Nums, 2048),
    (wR8fR86pGT6Labs, wR8fR86pGT6Nums, 2048), (wR8fR86pGT7Labs, wR8fR86pGT7Nums, 2048),
    (wR8fR86pGT8Labs, wR8fR86pGT8Nums, 2048), (wR8fR86pGT9Labs, wR8fR86pGT9Nums, 2048),
    (wR8fR86pGT10Labs, wR8fR86pGT10Nums, 2048), (wR8fR86pGT11Labs, wR8fR86pGT11Nums, 2048),
    (wR8fR86pGT12Labs, wR8fR86pGT12Nums, 2048), (wR8fR86pGT13Labs, wR8fR86pGT13Nums, 2048),
    (wR8fR86pGT14Labs, wR8fR86pGT14Nums, 2048), (wR8fR86pGT15Labs, wR8fR86pGT15Nums, 2048),
    (wR8fR86pGT16Labs, wR8fR86pGT16Nums, 2048), (wR8fR86pGT17Labs, wR8fR86pGT17Nums, 2048),
    (wR8fR86pGT18Labs, wR8fR86pGT18Nums, 2048), (wR8fR86pGT19Labs, wR8fR86pGT19Nums, 2048),
    (wR8fR86pGT20Labs, wR8fR86pGT20Nums, 2048), (wR8fR86pGT21Labs, wR8fR86pGT21Nums, 2048),
    (wR8fR86pGT22Labs, wR8fR86pGT22Nums, 1704)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wR8fR86p_hok : octPackOk 64 wR8fR86pL = true :=
  OctadDense.octPackOk_of_chk 64 6 true wR8fR86pL _ _ 4048896 wR8fR86p_Lsh wR8fR86p_chk

/-- The octad integer sum. -/
theorem wR8fR86p_octn : octSumZ 64 true wR8fR86pL wR8fR86pW = 4048896 :=
  OctadDense.octSumZ_of_chk 64 6 true wR8fR86pL wR8fR86pW _ _ 4048896 wR8fR86p_Lsh wR8fR86p_Wsh
      wR8fR86p_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wR8fR86p_selfchk : OctadDense.selfOctChk 64 [(wR8fR86pGT0Labs, wR8fR86pGT0Nums, 2048),
    (wR8fR86pGT1Labs, wR8fR86pGT1Nums, 2048), (wR8fR86pGT2Labs, wR8fR86pGT2Nums, 2048),
    (wR8fR86pGT3Labs, wR8fR86pGT3Nums, 2048), (wR8fR86pGT4Labs, wR8fR86pGT4Nums, 2048),
    (wR8fR86pGT5Labs, wR8fR86pGT5Nums, 2048), (wR8fR86pGT6Labs, wR8fR86pGT6Nums, 2048),
    (wR8fR86pGT7Labs, wR8fR86pGT7Nums, 2048), (wR8fR86pGT8Labs, wR8fR86pGT8Nums, 2048),
    (wR8fR86pGT9Labs, wR8fR86pGT9Nums, 2048), (wR8fR86pGT10Labs, wR8fR86pGT10Nums, 2048),
    (wR8fR86pGT11Labs, wR8fR86pGT11Nums, 2048), (wR8fR86pGT12Labs, wR8fR86pGT12Nums, 2048),
    (wR8fR86pGT13Labs, wR8fR86pGT13Nums, 2048), (wR8fR86pGT14Labs, wR8fR86pGT14Nums, 2048),
    (wR8fR86pGT15Labs, wR8fR86pGT15Nums, 2048), (wR8fR86pGT16Labs, wR8fR86pGT16Nums, 2048),
    (wR8fR86pGT17Labs, wR8fR86pGT17Nums, 2048), (wR8fR86pGT18Labs, wR8fR86pGT18Nums, 2048),
    (wR8fR86pGT19Labs, wR8fR86pGT19Nums, 2048), (wR8fR86pGT20Labs, wR8fR86pGT20Nums, 2048),
    (wR8fR86pGT21Labs, wR8fR86pGT21Nums, 2048), (wR8fR86pGT22Labs, wR8fR86pGT22Nums, 1704)] 506112
    = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wR8fR86p_hn : wR8fR86pL.sden * (octSumZ 64 true wR8fR86pL wR8fR86pW : ℚ) / 8 =
    wR8fR86pW.sden * (selfOctP wR8fR86pW : ℚ) := by
  rw [wR8fR86p_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wR8fR86pW _ 506112 wR8fR86p_Wsh
      wR8fR86p_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
