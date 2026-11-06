/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR87nTChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octads) of the identification Root8[8]- <-> Tenth[51]- (record r8f:R87-, e =
-1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wR8fR87nT_chk : OctadDense.octSumChk 64 7 false [(wR8fR87nTHT0Labs, wR8fR87nTHT0Nums,
    2048), (wR8fR87nTHT1Labs, wR8fR87nTHT1Nums, 2048), (wR8fR87nTHT2Labs, wR8fR87nTHT2Nums, 2048),
    (wR8fR87nTHT3Labs, wR8fR87nTHT3Nums, 2048), (wR8fR87nTHT4Labs, wR8fR87nTHT4Nums, 2048),
    (wR8fR87nTHT5Labs, wR8fR87nTHT5Nums, 2048), (wR8fR87nTHT6Labs, wR8fR87nTHT6Nums, 2048),
    (wR8fR87nTHT7Labs, wR8fR87nTHT7Nums, 2048), (wR8fR87nTHT8Labs, wR8fR87nTHT8Nums, 2048),
    (wR8fR87nTHT9Labs, wR8fR87nTHT9Nums, 2048), (wR8fR87nTHT10Labs, wR8fR87nTHT10Nums, 2048),
    (wR8fR87nTHT11Labs, wR8fR87nTHT11Nums, 2048), (wR8fR87nTHT12Labs, wR8fR87nTHT12Nums, 2048),
    (wR8fR87nTHT13Labs, wR8fR87nTHT13Nums, 2048), (wR8fR87nTHT14Labs, wR8fR87nTHT14Nums, 2048),
    (wR8fR87nTHT15Labs, wR8fR87nTHT15Nums, 2048), (wR8fR87nTHT16Labs, wR8fR87nTHT16Nums, 808)]
    [(wR8fR87nTGT0Labs, wR8fR87nTGT0Nums, 2048), (wR8fR87nTGT1Labs, wR8fR87nTGT1Nums, 2048),
    (wR8fR87nTGT2Labs, wR8fR87nTGT2Nums, 2048), (wR8fR87nTGT3Labs, wR8fR87nTGT3Nums, 2048),
    (wR8fR87nTGT4Labs, wR8fR87nTGT4Nums, 2048), (wR8fR87nTGT5Labs, wR8fR87nTGT5Nums, 2048),
    (wR8fR87nTGT6Labs, wR8fR87nTGT6Nums, 2048), (wR8fR87nTGT7Labs, wR8fR87nTGT7Nums, 2048),
    (wR8fR87nTGT8Labs, wR8fR87nTGT8Nums, 2048), (wR8fR87nTGT9Labs, wR8fR87nTGT9Nums, 2048),
    (wR8fR87nTGT10Labs, wR8fR87nTGT10Nums, 2048), (wR8fR87nTGT11Labs, wR8fR87nTGT11Nums, 2048),
    (wR8fR87nTGT12Labs, wR8fR87nTGT12Nums, 2048), (wR8fR87nTGT13Labs, wR8fR87nTGT13Nums, 2048),
    (wR8fR87nTGT14Labs, wR8fR87nTGT14Nums, 2048), (wR8fR87nTGT15Labs, wR8fR87nTGT15Nums, 2048),
    (wR8fR87nTGT16Labs, wR8fR87nTGT16Nums, 2048), (wR8fR87nTGT17Labs, wR8fR87nTGT17Nums, 2048),
    (wR8fR87nTGT18Labs, wR8fR87nTGT18Nums, 2048), (wR8fR87nTGT19Labs, wR8fR87nTGT19Nums, 2048),
    (wR8fR87nTGT20Labs, wR8fR87nTGT20Nums, 2048), (wR8fR87nTGT21Labs, wR8fR87nTGT21Nums, 2048),
    (wR8fR87nTGT22Labs, wR8fR87nTGT22Nums, 1026)] 4012032 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wR8fR87nT_Lsh : wR8fR87nTL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR87nTHT0Labs, wR8fR87nTHT0Nums, 2048), (wR8fR87nTHT1Labs, wR8fR87nTHT1Nums, 2048),
    (wR8fR87nTHT2Labs, wR8fR87nTHT2Nums, 2048), (wR8fR87nTHT3Labs, wR8fR87nTHT3Nums, 2048),
    (wR8fR87nTHT4Labs, wR8fR87nTHT4Nums, 2048), (wR8fR87nTHT5Labs, wR8fR87nTHT5Nums, 2048),
    (wR8fR87nTHT6Labs, wR8fR87nTHT6Nums, 2048), (wR8fR87nTHT7Labs, wR8fR87nTHT7Nums, 2048),
    (wR8fR87nTHT8Labs, wR8fR87nTHT8Nums, 2048), (wR8fR87nTHT9Labs, wR8fR87nTHT9Nums, 2048),
    (wR8fR87nTHT10Labs, wR8fR87nTHT10Nums, 2048), (wR8fR87nTHT11Labs, wR8fR87nTHT11Nums, 2048),
    (wR8fR87nTHT12Labs, wR8fR87nTHT12Nums, 2048), (wR8fR87nTHT13Labs, wR8fR87nTHT13Nums, 2048),
    (wR8fR87nTHT14Labs, wR8fR87nTHT14Nums, 2048), (wR8fR87nTHT15Labs, wR8fR87nTHT15Nums, 2048),
    (wR8fR87nTHT16Labs, wR8fR87nTHT16Nums, 808)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wR8fR87nT_Wsh : wR8fR87nTW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR87nTGT0Labs, wR8fR87nTGT0Nums, 2048), (wR8fR87nTGT1Labs, wR8fR87nTGT1Nums, 2048),
    (wR8fR87nTGT2Labs, wR8fR87nTGT2Nums, 2048), (wR8fR87nTGT3Labs, wR8fR87nTGT3Nums, 2048),
    (wR8fR87nTGT4Labs, wR8fR87nTGT4Nums, 2048), (wR8fR87nTGT5Labs, wR8fR87nTGT5Nums, 2048),
    (wR8fR87nTGT6Labs, wR8fR87nTGT6Nums, 2048), (wR8fR87nTGT7Labs, wR8fR87nTGT7Nums, 2048),
    (wR8fR87nTGT8Labs, wR8fR87nTGT8Nums, 2048), (wR8fR87nTGT9Labs, wR8fR87nTGT9Nums, 2048),
    (wR8fR87nTGT10Labs, wR8fR87nTGT10Nums, 2048), (wR8fR87nTGT11Labs, wR8fR87nTGT11Nums, 2048),
    (wR8fR87nTGT12Labs, wR8fR87nTGT12Nums, 2048), (wR8fR87nTGT13Labs, wR8fR87nTGT13Nums, 2048),
    (wR8fR87nTGT14Labs, wR8fR87nTGT14Nums, 2048), (wR8fR87nTGT15Labs, wR8fR87nTGT15Nums, 2048),
    (wR8fR87nTGT16Labs, wR8fR87nTGT16Nums, 2048), (wR8fR87nTGT17Labs, wR8fR87nTGT17Nums, 2048),
    (wR8fR87nTGT18Labs, wR8fR87nTGT18Nums, 2048), (wR8fR87nTGT19Labs, wR8fR87nTGT19Nums, 2048),
    (wR8fR87nTGT20Labs, wR8fR87nTGT20Nums, 2048), (wR8fR87nTGT21Labs, wR8fR87nTGT21Nums, 2048),
    (wR8fR87nTGT22Labs, wR8fR87nTGT22Nums, 1026)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wR8fR87nT_hok : octPackOk 64 wR8fR87nTL = true :=
  OctadDense.octPackOk_of_chk 64 7 false wR8fR87nTL _ _ 4012032 wR8fR87nT_Lsh wR8fR87nT_chk

/-- The octad integer sum. -/
theorem wR8fR87nT_octn : octSumZ 64 false wR8fR87nTL wR8fR87nTW = 4012032 :=
  OctadDense.octSumZ_of_chk 64 7 false wR8fR87nTL wR8fR87nTW _ _ 4012032 wR8fR87nT_Lsh
      wR8fR87nT_Wsh wR8fR87nT_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wR8fR87nT_selfchk : OctadDense.selfOctChk 64 [(wR8fR87nTGT0Labs, wR8fR87nTGT0Nums, 2048),
    (wR8fR87nTGT1Labs, wR8fR87nTGT1Nums, 2048), (wR8fR87nTGT2Labs, wR8fR87nTGT2Nums, 2048),
    (wR8fR87nTGT3Labs, wR8fR87nTGT3Nums, 2048), (wR8fR87nTGT4Labs, wR8fR87nTGT4Nums, 2048),
    (wR8fR87nTGT5Labs, wR8fR87nTGT5Nums, 2048), (wR8fR87nTGT6Labs, wR8fR87nTGT6Nums, 2048),
    (wR8fR87nTGT7Labs, wR8fR87nTGT7Nums, 2048), (wR8fR87nTGT8Labs, wR8fR87nTGT8Nums, 2048),
    (wR8fR87nTGT9Labs, wR8fR87nTGT9Nums, 2048), (wR8fR87nTGT10Labs, wR8fR87nTGT10Nums, 2048),
    (wR8fR87nTGT11Labs, wR8fR87nTGT11Nums, 2048), (wR8fR87nTGT12Labs, wR8fR87nTGT12Nums, 2048),
    (wR8fR87nTGT13Labs, wR8fR87nTGT13Nums, 2048), (wR8fR87nTGT14Labs, wR8fR87nTGT14Nums, 2048),
    (wR8fR87nTGT15Labs, wR8fR87nTGT15Nums, 2048), (wR8fR87nTGT16Labs, wR8fR87nTGT16Nums, 2048),
    (wR8fR87nTGT17Labs, wR8fR87nTGT17Nums, 2048), (wR8fR87nTGT18Labs, wR8fR87nTGT18Nums, 2048),
    (wR8fR87nTGT19Labs, wR8fR87nTGT19Nums, 2048), (wR8fR87nTGT20Labs, wR8fR87nTGT20Nums, 2048),
    (wR8fR87nTGT21Labs, wR8fR87nTGT21Nums, 2048), (wR8fR87nTGT22Labs, wR8fR87nTGT22Nums, 1026)]
    501504 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wR8fR87nT_hn : wR8fR87nTL.sden * (octSumZ 64 false wR8fR87nTL wR8fR87nTW : ℚ) / 8 =
    wR8fR87nTW.sden * (selfOctP wR8fR87nTW : ℚ) := by
  rw [wR8fR87nT_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wR8fR87nTW _ 501504 wR8fR87nT_Wsh
      wR8fR87nT_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
