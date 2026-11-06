/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR811nTChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Factory parts (octads) of the identification Root8[13]- <-> Root8[13]- (record r8f:R811-, e
= -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wR8fR811nT_chk : OctadDense.octSumChk 64 6 false [(wR8fR811nTHT0Labs, wR8fR811nTHT0Nums,
    2048), (wR8fR811nTHT1Labs, wR8fR811nTHT1Nums, 2048), (wR8fR811nTHT2Labs, wR8fR811nTHT2Nums,
    2048), (wR8fR811nTHT3Labs, wR8fR811nTHT3Nums, 2048), (wR8fR811nTHT4Labs, wR8fR811nTHT4Nums,
    2048), (wR8fR811nTHT5Labs, wR8fR811nTHT5Nums, 2048), (wR8fR811nTHT6Labs, wR8fR811nTHT6Nums,
    2048), (wR8fR811nTHT7Labs, wR8fR811nTHT7Nums, 2048), (wR8fR811nTHT8Labs, wR8fR811nTHT8Nums,
    2048), (wR8fR811nTHT9Labs, wR8fR811nTHT9Nums, 2048), (wR8fR811nTHT10Labs, wR8fR811nTHT10Nums,
    2048), (wR8fR811nTHT11Labs, wR8fR811nTHT11Nums, 2048), (wR8fR811nTHT12Labs,
    wR8fR811nTHT12Nums, 2048), (wR8fR811nTHT13Labs, wR8fR811nTHT13Nums, 2048),
    (wR8fR811nTHT14Labs, wR8fR811nTHT14Nums, 2048), (wR8fR811nTHT15Labs, wR8fR811nTHT15Nums,
    2048), (wR8fR811nTHT16Labs, wR8fR811nTHT16Nums, 808)] [(wR8fR811nTGT0Labs, wR8fR811nTGT0Nums,
    2048), (wR8fR811nTGT1Labs, wR8fR811nTGT1Nums, 2048), (wR8fR811nTGT2Labs, wR8fR811nTGT2Nums,
    2048), (wR8fR811nTGT3Labs, wR8fR811nTGT3Nums, 2048), (wR8fR811nTGT4Labs, wR8fR811nTGT4Nums,
    2048), (wR8fR811nTGT5Labs, wR8fR811nTGT5Nums, 2048), (wR8fR811nTGT6Labs, wR8fR811nTGT6Nums,
    2048), (wR8fR811nTGT7Labs, wR8fR811nTGT7Nums, 2048), (wR8fR811nTGT8Labs, wR8fR811nTGT8Nums,
    2048), (wR8fR811nTGT9Labs, wR8fR811nTGT9Nums, 2048), (wR8fR811nTGT10Labs, wR8fR811nTGT10Nums,
    2048), (wR8fR811nTGT11Labs, wR8fR811nTGT11Nums, 2048), (wR8fR811nTGT12Labs,
    wR8fR811nTGT12Nums, 2048), (wR8fR811nTGT13Labs, wR8fR811nTGT13Nums, 2048),
    (wR8fR811nTGT14Labs, wR8fR811nTGT14Nums, 2048), (wR8fR811nTGT15Labs, wR8fR811nTGT15Nums,
    2048), (wR8fR811nTGT16Labs, wR8fR811nTGT16Nums, 808)] 4050944 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wR8fR811nT_Lsh : wR8fR811nTL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR811nTHT0Labs, wR8fR811nTHT0Nums, 2048), (wR8fR811nTHT1Labs, wR8fR811nTHT1Nums, 2048),
    (wR8fR811nTHT2Labs, wR8fR811nTHT2Nums, 2048), (wR8fR811nTHT3Labs, wR8fR811nTHT3Nums, 2048),
    (wR8fR811nTHT4Labs, wR8fR811nTHT4Nums, 2048), (wR8fR811nTHT5Labs, wR8fR811nTHT5Nums, 2048),
    (wR8fR811nTHT6Labs, wR8fR811nTHT6Nums, 2048), (wR8fR811nTHT7Labs, wR8fR811nTHT7Nums, 2048),
    (wR8fR811nTHT8Labs, wR8fR811nTHT8Nums, 2048), (wR8fR811nTHT9Labs, wR8fR811nTHT9Nums, 2048),
    (wR8fR811nTHT10Labs, wR8fR811nTHT10Nums, 2048), (wR8fR811nTHT11Labs, wR8fR811nTHT11Nums,
    2048), (wR8fR811nTHT12Labs, wR8fR811nTHT12Nums, 2048), (wR8fR811nTHT13Labs,
    wR8fR811nTHT13Nums, 2048), (wR8fR811nTHT14Labs, wR8fR811nTHT14Nums, 2048),
    (wR8fR811nTHT15Labs, wR8fR811nTHT15Nums, 2048), (wR8fR811nTHT16Labs, wR8fR811nTHT16Nums,
    808)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wR8fR811nT_Wsh : wR8fR811nTW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR811nTGT0Labs, wR8fR811nTGT0Nums, 2048), (wR8fR811nTGT1Labs, wR8fR811nTGT1Nums, 2048),
    (wR8fR811nTGT2Labs, wR8fR811nTGT2Nums, 2048), (wR8fR811nTGT3Labs, wR8fR811nTGT3Nums, 2048),
    (wR8fR811nTGT4Labs, wR8fR811nTGT4Nums, 2048), (wR8fR811nTGT5Labs, wR8fR811nTGT5Nums, 2048),
    (wR8fR811nTGT6Labs, wR8fR811nTGT6Nums, 2048), (wR8fR811nTGT7Labs, wR8fR811nTGT7Nums, 2048),
    (wR8fR811nTGT8Labs, wR8fR811nTGT8Nums, 2048), (wR8fR811nTGT9Labs, wR8fR811nTGT9Nums, 2048),
    (wR8fR811nTGT10Labs, wR8fR811nTGT10Nums, 2048), (wR8fR811nTGT11Labs, wR8fR811nTGT11Nums,
    2048), (wR8fR811nTGT12Labs, wR8fR811nTGT12Nums, 2048), (wR8fR811nTGT13Labs,
    wR8fR811nTGT13Nums, 2048), (wR8fR811nTGT14Labs, wR8fR811nTGT14Nums, 2048),
    (wR8fR811nTGT15Labs, wR8fR811nTGT15Nums, 2048), (wR8fR811nTGT16Labs, wR8fR811nTGT16Nums,
    808)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wR8fR811nT_hok : octPackOk 64 wR8fR811nTL = true :=
  OctadDense.octPackOk_of_chk 64 6 false wR8fR811nTL _ _ 4050944 wR8fR811nT_Lsh wR8fR811nT_chk

/-- The octad integer sum. -/
theorem wR8fR811nT_octn : octSumZ 64 false wR8fR811nTL wR8fR811nTW = 4050944 :=
  OctadDense.octSumZ_of_chk 64 6 false wR8fR811nTL wR8fR811nTW _ _ 4050944 wR8fR811nT_Lsh
      wR8fR811nT_Wsh wR8fR811nT_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wR8fR811nT_selfchk : OctadDense.selfOctChk 64 [(wR8fR811nTGT0Labs, wR8fR811nTGT0Nums,
    2048), (wR8fR811nTGT1Labs, wR8fR811nTGT1Nums, 2048), (wR8fR811nTGT2Labs, wR8fR811nTGT2Nums,
    2048), (wR8fR811nTGT3Labs, wR8fR811nTGT3Nums, 2048), (wR8fR811nTGT4Labs, wR8fR811nTGT4Nums,
    2048), (wR8fR811nTGT5Labs, wR8fR811nTGT5Nums, 2048), (wR8fR811nTGT6Labs, wR8fR811nTGT6Nums,
    2048), (wR8fR811nTGT7Labs, wR8fR811nTGT7Nums, 2048), (wR8fR811nTGT8Labs, wR8fR811nTGT8Nums,
    2048), (wR8fR811nTGT9Labs, wR8fR811nTGT9Nums, 2048), (wR8fR811nTGT10Labs, wR8fR811nTGT10Nums,
    2048), (wR8fR811nTGT11Labs, wR8fR811nTGT11Nums, 2048), (wR8fR811nTGT12Labs,
    wR8fR811nTGT12Nums, 2048), (wR8fR811nTGT13Labs, wR8fR811nTGT13Nums, 2048),
    (wR8fR811nTGT14Labs, wR8fR811nTGT14Nums, 2048), (wR8fR811nTGT15Labs, wR8fR811nTGT15Nums,
    2048), (wR8fR811nTGT16Labs, wR8fR811nTGT16Nums, 808)] 506368 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wR8fR811nT_hn : wR8fR811nTL.sden * (octSumZ 64 false wR8fR811nTL wR8fR811nTW : ℚ) / 8 =
    wR8fR811nTW.sden * (selfOctP wR8fR811nTW : ℚ) := by
  rw [wR8fR811nT_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wR8fR811nTW _ 506368
      wR8fR811nT_Wsh wR8fR811nT_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
