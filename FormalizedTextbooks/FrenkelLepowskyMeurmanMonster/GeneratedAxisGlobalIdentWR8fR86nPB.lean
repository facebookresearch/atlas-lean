/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (octads) of the identification Root8[12]- <-> Twelfth[34]- (record r8f:R86-, e
= -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wR8fR86n_chk : OctadDense.octSumChk 64 6 false [(wR8fR86nHT0Labs, wR8fR86nHT0Nums, 2048),
    (wR8fR86nHT1Labs, wR8fR86nHT1Nums, 2048), (wR8fR86nHT2Labs, wR8fR86nHT2Nums, 2048),
    (wR8fR86nHT3Labs, wR8fR86nHT3Nums, 2048), (wR8fR86nHT4Labs, wR8fR86nHT4Nums, 2048),
    (wR8fR86nHT5Labs, wR8fR86nHT5Nums, 2048), (wR8fR86nHT6Labs, wR8fR86nHT6Nums, 2048),
    (wR8fR86nHT7Labs, wR8fR86nHT7Nums, 2048), (wR8fR86nHT8Labs, wR8fR86nHT8Nums, 2048),
    (wR8fR86nHT9Labs, wR8fR86nHT9Nums, 2048), (wR8fR86nHT10Labs, wR8fR86nHT10Nums, 2048),
    (wR8fR86nHT11Labs, wR8fR86nHT11Nums, 2048), (wR8fR86nHT12Labs, wR8fR86nHT12Nums, 2048),
    (wR8fR86nHT13Labs, wR8fR86nHT13Nums, 2048), (wR8fR86nHT14Labs, wR8fR86nHT14Nums, 2048),
    (wR8fR86nHT15Labs, wR8fR86nHT15Nums, 2048), (wR8fR86nHT16Labs, wR8fR86nHT16Nums, 808)]
    [(wR8fR86nGT0Labs, wR8fR86nGT0Nums, 2048), (wR8fR86nGT1Labs, wR8fR86nGT1Nums, 2048),
    (wR8fR86nGT2Labs, wR8fR86nGT2Nums, 2048), (wR8fR86nGT3Labs, wR8fR86nGT3Nums, 2048),
    (wR8fR86nGT4Labs, wR8fR86nGT4Nums, 2048), (wR8fR86nGT5Labs, wR8fR86nGT5Nums, 2048),
    (wR8fR86nGT6Labs, wR8fR86nGT6Nums, 2048), (wR8fR86nGT7Labs, wR8fR86nGT7Nums, 2048),
    (wR8fR86nGT8Labs, wR8fR86nGT8Nums, 2048), (wR8fR86nGT9Labs, wR8fR86nGT9Nums, 2048),
    (wR8fR86nGT10Labs, wR8fR86nGT10Nums, 2048), (wR8fR86nGT11Labs, wR8fR86nGT11Nums, 2048),
    (wR8fR86nGT12Labs, wR8fR86nGT12Nums, 2048), (wR8fR86nGT13Labs, wR8fR86nGT13Nums, 2048),
    (wR8fR86nGT14Labs, wR8fR86nGT14Nums, 2048), (wR8fR86nGT15Labs, wR8fR86nGT15Nums, 2048),
    (wR8fR86nGT16Labs, wR8fR86nGT16Nums, 2048), (wR8fR86nGT17Labs, wR8fR86nGT17Nums, 2048),
    (wR8fR86nGT18Labs, wR8fR86nGT18Nums, 2048), (wR8fR86nGT19Labs, wR8fR86nGT19Nums, 2048),
    (wR8fR86nGT20Labs, wR8fR86nGT20Nums, 2048), (wR8fR86nGT21Labs, wR8fR86nGT21Nums, 2048),
    (wR8fR86nGT22Labs, wR8fR86nGT22Nums, 1704)] 4048896 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wR8fR86n_Lsh : wR8fR86nL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR86nHT0Labs, wR8fR86nHT0Nums, 2048), (wR8fR86nHT1Labs, wR8fR86nHT1Nums, 2048),
    (wR8fR86nHT2Labs, wR8fR86nHT2Nums, 2048), (wR8fR86nHT3Labs, wR8fR86nHT3Nums, 2048),
    (wR8fR86nHT4Labs, wR8fR86nHT4Nums, 2048), (wR8fR86nHT5Labs, wR8fR86nHT5Nums, 2048),
    (wR8fR86nHT6Labs, wR8fR86nHT6Nums, 2048), (wR8fR86nHT7Labs, wR8fR86nHT7Nums, 2048),
    (wR8fR86nHT8Labs, wR8fR86nHT8Nums, 2048), (wR8fR86nHT9Labs, wR8fR86nHT9Nums, 2048),
    (wR8fR86nHT10Labs, wR8fR86nHT10Nums, 2048), (wR8fR86nHT11Labs, wR8fR86nHT11Nums, 2048),
    (wR8fR86nHT12Labs, wR8fR86nHT12Nums, 2048), (wR8fR86nHT13Labs, wR8fR86nHT13Nums, 2048),
    (wR8fR86nHT14Labs, wR8fR86nHT14Nums, 2048), (wR8fR86nHT15Labs, wR8fR86nHT15Nums, 2048),
    (wR8fR86nHT16Labs, wR8fR86nHT16Nums, 808)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wR8fR86n_Wsh : wR8fR86nW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR86nGT0Labs, wR8fR86nGT0Nums, 2048), (wR8fR86nGT1Labs, wR8fR86nGT1Nums, 2048),
    (wR8fR86nGT2Labs, wR8fR86nGT2Nums, 2048), (wR8fR86nGT3Labs, wR8fR86nGT3Nums, 2048),
    (wR8fR86nGT4Labs, wR8fR86nGT4Nums, 2048), (wR8fR86nGT5Labs, wR8fR86nGT5Nums, 2048),
    (wR8fR86nGT6Labs, wR8fR86nGT6Nums, 2048), (wR8fR86nGT7Labs, wR8fR86nGT7Nums, 2048),
    (wR8fR86nGT8Labs, wR8fR86nGT8Nums, 2048), (wR8fR86nGT9Labs, wR8fR86nGT9Nums, 2048),
    (wR8fR86nGT10Labs, wR8fR86nGT10Nums, 2048), (wR8fR86nGT11Labs, wR8fR86nGT11Nums, 2048),
    (wR8fR86nGT12Labs, wR8fR86nGT12Nums, 2048), (wR8fR86nGT13Labs, wR8fR86nGT13Nums, 2048),
    (wR8fR86nGT14Labs, wR8fR86nGT14Nums, 2048), (wR8fR86nGT15Labs, wR8fR86nGT15Nums, 2048),
    (wR8fR86nGT16Labs, wR8fR86nGT16Nums, 2048), (wR8fR86nGT17Labs, wR8fR86nGT17Nums, 2048),
    (wR8fR86nGT18Labs, wR8fR86nGT18Nums, 2048), (wR8fR86nGT19Labs, wR8fR86nGT19Nums, 2048),
    (wR8fR86nGT20Labs, wR8fR86nGT20Nums, 2048), (wR8fR86nGT21Labs, wR8fR86nGT21Nums, 2048),
    (wR8fR86nGT22Labs, wR8fR86nGT22Nums, 1704)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wR8fR86n_hok : octPackOk 64 wR8fR86nL = true :=
  OctadDense.octPackOk_of_chk 64 6 false wR8fR86nL _ _ 4048896 wR8fR86n_Lsh wR8fR86n_chk

/-- The octad integer sum. -/
theorem wR8fR86n_octn : octSumZ 64 false wR8fR86nL wR8fR86nW = 4048896 :=
  OctadDense.octSumZ_of_chk 64 6 false wR8fR86nL wR8fR86nW _ _ 4048896 wR8fR86n_Lsh wR8fR86n_Wsh
      wR8fR86n_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wR8fR86n_selfchk : OctadDense.selfOctChk 64 [(wR8fR86nGT0Labs, wR8fR86nGT0Nums, 2048),
    (wR8fR86nGT1Labs, wR8fR86nGT1Nums, 2048), (wR8fR86nGT2Labs, wR8fR86nGT2Nums, 2048),
    (wR8fR86nGT3Labs, wR8fR86nGT3Nums, 2048), (wR8fR86nGT4Labs, wR8fR86nGT4Nums, 2048),
    (wR8fR86nGT5Labs, wR8fR86nGT5Nums, 2048), (wR8fR86nGT6Labs, wR8fR86nGT6Nums, 2048),
    (wR8fR86nGT7Labs, wR8fR86nGT7Nums, 2048), (wR8fR86nGT8Labs, wR8fR86nGT8Nums, 2048),
    (wR8fR86nGT9Labs, wR8fR86nGT9Nums, 2048), (wR8fR86nGT10Labs, wR8fR86nGT10Nums, 2048),
    (wR8fR86nGT11Labs, wR8fR86nGT11Nums, 2048), (wR8fR86nGT12Labs, wR8fR86nGT12Nums, 2048),
    (wR8fR86nGT13Labs, wR8fR86nGT13Nums, 2048), (wR8fR86nGT14Labs, wR8fR86nGT14Nums, 2048),
    (wR8fR86nGT15Labs, wR8fR86nGT15Nums, 2048), (wR8fR86nGT16Labs, wR8fR86nGT16Nums, 2048),
    (wR8fR86nGT17Labs, wR8fR86nGT17Nums, 2048), (wR8fR86nGT18Labs, wR8fR86nGT18Nums, 2048),
    (wR8fR86nGT19Labs, wR8fR86nGT19Nums, 2048), (wR8fR86nGT20Labs, wR8fR86nGT20Nums, 2048),
    (wR8fR86nGT21Labs, wR8fR86nGT21Nums, 2048), (wR8fR86nGT22Labs, wR8fR86nGT22Nums, 1704)] 506112
    = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wR8fR86n_hn : wR8fR86nL.sden * (octSumZ 64 false wR8fR86nL wR8fR86nW : ℚ) / 8 =
    wR8fR86nW.sden * (selfOctP wR8fR86nW : ℚ) := by
  rw [wR8fR86n_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wR8fR86nW _ 506112 wR8fR86n_Wsh
      wR8fR86n_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
