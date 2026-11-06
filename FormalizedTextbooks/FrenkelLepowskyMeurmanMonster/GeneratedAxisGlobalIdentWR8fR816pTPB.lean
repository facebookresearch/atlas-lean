/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR816pTChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Factory parts (octads) of the identification Root8[22]+ <-> Root8[22]+ (record r8f:R816+, e
= 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wR8fR816pT_chk : OctadDense.octSumChk 64 6 true [(wR8fR816pTHT0Labs, wR8fR816pTHT0Nums,
    2048), (wR8fR816pTHT1Labs, wR8fR816pTHT1Nums, 2048), (wR8fR816pTHT2Labs, wR8fR816pTHT2Nums,
    2048), (wR8fR816pTHT3Labs, wR8fR816pTHT3Nums, 2048), (wR8fR816pTHT4Labs, wR8fR816pTHT4Nums,
    2048), (wR8fR816pTHT5Labs, wR8fR816pTHT5Nums, 2048), (wR8fR816pTHT6Labs, wR8fR816pTHT6Nums,
    2048), (wR8fR816pTHT7Labs, wR8fR816pTHT7Nums, 2048), (wR8fR816pTHT8Labs, wR8fR816pTHT8Nums,
    2048), (wR8fR816pTHT9Labs, wR8fR816pTHT9Nums, 2048), (wR8fR816pTHT10Labs, wR8fR816pTHT10Nums,
    2048), (wR8fR816pTHT11Labs, wR8fR816pTHT11Nums, 2048), (wR8fR816pTHT12Labs,
    wR8fR816pTHT12Nums, 2048), (wR8fR816pTHT13Labs, wR8fR816pTHT13Nums, 2048),
    (wR8fR816pTHT14Labs, wR8fR816pTHT14Nums, 2048), (wR8fR816pTHT15Labs, wR8fR816pTHT15Nums,
    2048), (wR8fR816pTHT16Labs, wR8fR816pTHT16Nums, 808)] [(wR8fR816pTGT0Labs, wR8fR816pTGT0Nums,
    2048), (wR8fR816pTGT1Labs, wR8fR816pTGT1Nums, 2048), (wR8fR816pTGT2Labs, wR8fR816pTGT2Nums,
    2048), (wR8fR816pTGT3Labs, wR8fR816pTGT3Nums, 2048), (wR8fR816pTGT4Labs, wR8fR816pTGT4Nums,
    2048), (wR8fR816pTGT5Labs, wR8fR816pTGT5Nums, 2048), (wR8fR816pTGT6Labs, wR8fR816pTGT6Nums,
    2048), (wR8fR816pTGT7Labs, wR8fR816pTGT7Nums, 2048), (wR8fR816pTGT8Labs, wR8fR816pTGT8Nums,
    2048), (wR8fR816pTGT9Labs, wR8fR816pTGT9Nums, 2048), (wR8fR816pTGT10Labs, wR8fR816pTGT10Nums,
    2048), (wR8fR816pTGT11Labs, wR8fR816pTGT11Nums, 2048), (wR8fR816pTGT12Labs,
    wR8fR816pTGT12Nums, 2048), (wR8fR816pTGT13Labs, wR8fR816pTGT13Nums, 2048),
    (wR8fR816pTGT14Labs, wR8fR816pTGT14Nums, 2048), (wR8fR816pTGT15Labs, wR8fR816pTGT15Nums,
    2048), (wR8fR816pTGT16Labs, wR8fR816pTGT16Nums, 808)] 4008960 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wR8fR816pT_Lsh : wR8fR816pTL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR816pTHT0Labs, wR8fR816pTHT0Nums, 2048), (wR8fR816pTHT1Labs, wR8fR816pTHT1Nums, 2048),
    (wR8fR816pTHT2Labs, wR8fR816pTHT2Nums, 2048), (wR8fR816pTHT3Labs, wR8fR816pTHT3Nums, 2048),
    (wR8fR816pTHT4Labs, wR8fR816pTHT4Nums, 2048), (wR8fR816pTHT5Labs, wR8fR816pTHT5Nums, 2048),
    (wR8fR816pTHT6Labs, wR8fR816pTHT6Nums, 2048), (wR8fR816pTHT7Labs, wR8fR816pTHT7Nums, 2048),
    (wR8fR816pTHT8Labs, wR8fR816pTHT8Nums, 2048), (wR8fR816pTHT9Labs, wR8fR816pTHT9Nums, 2048),
    (wR8fR816pTHT10Labs, wR8fR816pTHT10Nums, 2048), (wR8fR816pTHT11Labs, wR8fR816pTHT11Nums,
    2048), (wR8fR816pTHT12Labs, wR8fR816pTHT12Nums, 2048), (wR8fR816pTHT13Labs,
    wR8fR816pTHT13Nums, 2048), (wR8fR816pTHT14Labs, wR8fR816pTHT14Nums, 2048),
    (wR8fR816pTHT15Labs, wR8fR816pTHT15Nums, 2048), (wR8fR816pTHT16Labs, wR8fR816pTHT16Nums,
    808)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wR8fR816pT_Wsh : wR8fR816pTW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR816pTGT0Labs, wR8fR816pTGT0Nums, 2048), (wR8fR816pTGT1Labs, wR8fR816pTGT1Nums, 2048),
    (wR8fR816pTGT2Labs, wR8fR816pTGT2Nums, 2048), (wR8fR816pTGT3Labs, wR8fR816pTGT3Nums, 2048),
    (wR8fR816pTGT4Labs, wR8fR816pTGT4Nums, 2048), (wR8fR816pTGT5Labs, wR8fR816pTGT5Nums, 2048),
    (wR8fR816pTGT6Labs, wR8fR816pTGT6Nums, 2048), (wR8fR816pTGT7Labs, wR8fR816pTGT7Nums, 2048),
    (wR8fR816pTGT8Labs, wR8fR816pTGT8Nums, 2048), (wR8fR816pTGT9Labs, wR8fR816pTGT9Nums, 2048),
    (wR8fR816pTGT10Labs, wR8fR816pTGT10Nums, 2048), (wR8fR816pTGT11Labs, wR8fR816pTGT11Nums,
    2048), (wR8fR816pTGT12Labs, wR8fR816pTGT12Nums, 2048), (wR8fR816pTGT13Labs,
    wR8fR816pTGT13Nums, 2048), (wR8fR816pTGT14Labs, wR8fR816pTGT14Nums, 2048),
    (wR8fR816pTGT15Labs, wR8fR816pTGT15Nums, 2048), (wR8fR816pTGT16Labs, wR8fR816pTGT16Nums,
    808)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wR8fR816pT_hok : octPackOk 64 wR8fR816pTL = true :=
  OctadDense.octPackOk_of_chk 64 6 true wR8fR816pTL _ _ 4008960 wR8fR816pT_Lsh wR8fR816pT_chk

/-- The octad integer sum. -/
theorem wR8fR816pT_octn : octSumZ 64 true wR8fR816pTL wR8fR816pTW = 4008960 :=
  OctadDense.octSumZ_of_chk 64 6 true wR8fR816pTL wR8fR816pTW _ _ 4008960 wR8fR816pT_Lsh
      wR8fR816pT_Wsh wR8fR816pT_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wR8fR816pT_selfchk : OctadDense.selfOctChk 64 [(wR8fR816pTGT0Labs, wR8fR816pTGT0Nums,
    2048), (wR8fR816pTGT1Labs, wR8fR816pTGT1Nums, 2048), (wR8fR816pTGT2Labs, wR8fR816pTGT2Nums,
    2048), (wR8fR816pTGT3Labs, wR8fR816pTGT3Nums, 2048), (wR8fR816pTGT4Labs, wR8fR816pTGT4Nums,
    2048), (wR8fR816pTGT5Labs, wR8fR816pTGT5Nums, 2048), (wR8fR816pTGT6Labs, wR8fR816pTGT6Nums,
    2048), (wR8fR816pTGT7Labs, wR8fR816pTGT7Nums, 2048), (wR8fR816pTGT8Labs, wR8fR816pTGT8Nums,
    2048), (wR8fR816pTGT9Labs, wR8fR816pTGT9Nums, 2048), (wR8fR816pTGT10Labs, wR8fR816pTGT10Nums,
    2048), (wR8fR816pTGT11Labs, wR8fR816pTGT11Nums, 2048), (wR8fR816pTGT12Labs,
    wR8fR816pTGT12Nums, 2048), (wR8fR816pTGT13Labs, wR8fR816pTGT13Nums, 2048),
    (wR8fR816pTGT14Labs, wR8fR816pTGT14Nums, 2048), (wR8fR816pTGT15Labs, wR8fR816pTGT15Nums,
    2048), (wR8fR816pTGT16Labs, wR8fR816pTGT16Nums, 808)] 501120 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wR8fR816pT_hn : wR8fR816pTL.sden * (octSumZ 64 true wR8fR816pTL wR8fR816pTW : ℚ) / 8 =
    wR8fR816pTW.sden * (selfOctP wR8fR816pTW : ℚ) := by
  rw [wR8fR816pT_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wR8fR816pTW _ 501120
      wR8fR816pT_Wsh wR8fR816pT_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
