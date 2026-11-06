/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR821nwChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Factory parts (octads) of the identification Root8[33]- <-> Root8[33]- (record r8f:R821-, e
= -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wR8fR821nw_chk : OctadDense.octSumChk 64 6 false [(wR8fR821nwHT0Labs, wR8fR821nwHT0Nums,
    2048), (wR8fR821nwHT1Labs, wR8fR821nwHT1Nums, 2048), (wR8fR821nwHT2Labs, wR8fR821nwHT2Nums,
    2048), (wR8fR821nwHT3Labs, wR8fR821nwHT3Nums, 2048), (wR8fR821nwHT4Labs, wR8fR821nwHT4Nums,
    2048), (wR8fR821nwHT5Labs, wR8fR821nwHT5Nums, 2048), (wR8fR821nwHT6Labs, wR8fR821nwHT6Nums,
    2048), (wR8fR821nwHT7Labs, wR8fR821nwHT7Nums, 2048), (wR8fR821nwHT8Labs, wR8fR821nwHT8Nums,
    2048), (wR8fR821nwHT9Labs, wR8fR821nwHT9Nums, 2048), (wR8fR821nwHT10Labs, wR8fR821nwHT10Nums,
    2048), (wR8fR821nwHT11Labs, wR8fR821nwHT11Nums, 2048), (wR8fR821nwHT12Labs,
    wR8fR821nwHT12Nums, 2048), (wR8fR821nwHT13Labs, wR8fR821nwHT13Nums, 2048),
    (wR8fR821nwHT14Labs, wR8fR821nwHT14Nums, 2048), (wR8fR821nwHT15Labs, wR8fR821nwHT15Nums,
    2048), (wR8fR821nwHT16Labs, wR8fR821nwHT16Nums, 808)] [(wR8fR821nwGT0Labs, wR8fR821nwGT0Nums,
    2048), (wR8fR821nwGT1Labs, wR8fR821nwGT1Nums, 2048), (wR8fR821nwGT2Labs, wR8fR821nwGT2Nums,
    2048), (wR8fR821nwGT3Labs, wR8fR821nwGT3Nums, 2048), (wR8fR821nwGT4Labs, wR8fR821nwGT4Nums,
    2048), (wR8fR821nwGT5Labs, wR8fR821nwGT5Nums, 2048), (wR8fR821nwGT6Labs, wR8fR821nwGT6Nums,
    2048), (wR8fR821nwGT7Labs, wR8fR821nwGT7Nums, 2048), (wR8fR821nwGT8Labs, wR8fR821nwGT8Nums,
    2048), (wR8fR821nwGT9Labs, wR8fR821nwGT9Nums, 2048), (wR8fR821nwGT10Labs, wR8fR821nwGT10Nums,
    2048), (wR8fR821nwGT11Labs, wR8fR821nwGT11Nums, 2048), (wR8fR821nwGT12Labs,
    wR8fR821nwGT12Nums, 2048), (wR8fR821nwGT13Labs, wR8fR821nwGT13Nums, 2048),
    (wR8fR821nwGT14Labs, wR8fR821nwGT14Nums, 2048), (wR8fR821nwGT15Labs, wR8fR821nwGT15Nums,
    2048), (wR8fR821nwGT16Labs, wR8fR821nwGT16Nums, 808)] 4029952 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wR8fR821nw_Lsh : wR8fR821nwL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR821nwHT0Labs, wR8fR821nwHT0Nums, 2048), (wR8fR821nwHT1Labs, wR8fR821nwHT1Nums, 2048),
    (wR8fR821nwHT2Labs, wR8fR821nwHT2Nums, 2048), (wR8fR821nwHT3Labs, wR8fR821nwHT3Nums, 2048),
    (wR8fR821nwHT4Labs, wR8fR821nwHT4Nums, 2048), (wR8fR821nwHT5Labs, wR8fR821nwHT5Nums, 2048),
    (wR8fR821nwHT6Labs, wR8fR821nwHT6Nums, 2048), (wR8fR821nwHT7Labs, wR8fR821nwHT7Nums, 2048),
    (wR8fR821nwHT8Labs, wR8fR821nwHT8Nums, 2048), (wR8fR821nwHT9Labs, wR8fR821nwHT9Nums, 2048),
    (wR8fR821nwHT10Labs, wR8fR821nwHT10Nums, 2048), (wR8fR821nwHT11Labs, wR8fR821nwHT11Nums,
    2048), (wR8fR821nwHT12Labs, wR8fR821nwHT12Nums, 2048), (wR8fR821nwHT13Labs,
    wR8fR821nwHT13Nums, 2048), (wR8fR821nwHT14Labs, wR8fR821nwHT14Nums, 2048),
    (wR8fR821nwHT15Labs, wR8fR821nwHT15Nums, 2048), (wR8fR821nwHT16Labs, wR8fR821nwHT16Nums,
    808)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wR8fR821nw_Wsh : wR8fR821nwW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR821nwGT0Labs, wR8fR821nwGT0Nums, 2048), (wR8fR821nwGT1Labs, wR8fR821nwGT1Nums, 2048),
    (wR8fR821nwGT2Labs, wR8fR821nwGT2Nums, 2048), (wR8fR821nwGT3Labs, wR8fR821nwGT3Nums, 2048),
    (wR8fR821nwGT4Labs, wR8fR821nwGT4Nums, 2048), (wR8fR821nwGT5Labs, wR8fR821nwGT5Nums, 2048),
    (wR8fR821nwGT6Labs, wR8fR821nwGT6Nums, 2048), (wR8fR821nwGT7Labs, wR8fR821nwGT7Nums, 2048),
    (wR8fR821nwGT8Labs, wR8fR821nwGT8Nums, 2048), (wR8fR821nwGT9Labs, wR8fR821nwGT9Nums, 2048),
    (wR8fR821nwGT10Labs, wR8fR821nwGT10Nums, 2048), (wR8fR821nwGT11Labs, wR8fR821nwGT11Nums,
    2048), (wR8fR821nwGT12Labs, wR8fR821nwGT12Nums, 2048), (wR8fR821nwGT13Labs,
    wR8fR821nwGT13Nums, 2048), (wR8fR821nwGT14Labs, wR8fR821nwGT14Nums, 2048),
    (wR8fR821nwGT15Labs, wR8fR821nwGT15Nums, 2048), (wR8fR821nwGT16Labs, wR8fR821nwGT16Nums,
    808)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wR8fR821nw_hok : octPackOk 64 wR8fR821nwL = true :=
  OctadDense.octPackOk_of_chk 64 6 false wR8fR821nwL _ _ 4029952 wR8fR821nw_Lsh wR8fR821nw_chk

/-- The octad integer sum. -/
theorem wR8fR821nw_octn : octSumZ 64 false wR8fR821nwL wR8fR821nwW = 4029952 :=
  OctadDense.octSumZ_of_chk 64 6 false wR8fR821nwL wR8fR821nwW _ _ 4029952 wR8fR821nw_Lsh
      wR8fR821nw_Wsh wR8fR821nw_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wR8fR821nw_selfchk : OctadDense.selfOctChk 64 [(wR8fR821nwGT0Labs, wR8fR821nwGT0Nums,
    2048), (wR8fR821nwGT1Labs, wR8fR821nwGT1Nums, 2048), (wR8fR821nwGT2Labs, wR8fR821nwGT2Nums,
    2048), (wR8fR821nwGT3Labs, wR8fR821nwGT3Nums, 2048), (wR8fR821nwGT4Labs, wR8fR821nwGT4Nums,
    2048), (wR8fR821nwGT5Labs, wR8fR821nwGT5Nums, 2048), (wR8fR821nwGT6Labs, wR8fR821nwGT6Nums,
    2048), (wR8fR821nwGT7Labs, wR8fR821nwGT7Nums, 2048), (wR8fR821nwGT8Labs, wR8fR821nwGT8Nums,
    2048), (wR8fR821nwGT9Labs, wR8fR821nwGT9Nums, 2048), (wR8fR821nwGT10Labs, wR8fR821nwGT10Nums,
    2048), (wR8fR821nwGT11Labs, wR8fR821nwGT11Nums, 2048), (wR8fR821nwGT12Labs,
    wR8fR821nwGT12Nums, 2048), (wR8fR821nwGT13Labs, wR8fR821nwGT13Nums, 2048),
    (wR8fR821nwGT14Labs, wR8fR821nwGT14Nums, 2048), (wR8fR821nwGT15Labs, wR8fR821nwGT15Nums,
    2048), (wR8fR821nwGT16Labs, wR8fR821nwGT16Nums, 808)] 503744 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wR8fR821nw_hn : wR8fR821nwL.sden * (octSumZ 64 false wR8fR821nwL wR8fR821nwW : ℚ) / 8 =
    wR8fR821nwW.sden * (selfOctP wR8fR821nwW : ℚ) := by
  rw [wR8fR821nw_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wR8fR821nwW _ 503744
      wR8fR821nw_Wsh wR8fR821nw_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
