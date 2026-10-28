/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR83nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (octads) of the identification Root8[11]- <-> Twelfth[29]- (record r8f:R83-, e
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
theorem wR8fR83n_chk : OctadDense.octSumChk 64 6 false [(wR8fR83nHT0Labs, wR8fR83nHT0Nums, 2048),
    (wR8fR83nHT1Labs, wR8fR83nHT1Nums, 2048), (wR8fR83nHT2Labs, wR8fR83nHT2Nums, 2048),
    (wR8fR83nHT3Labs, wR8fR83nHT3Nums, 2048), (wR8fR83nHT4Labs, wR8fR83nHT4Nums, 2048),
    (wR8fR83nHT5Labs, wR8fR83nHT5Nums, 2048), (wR8fR83nHT6Labs, wR8fR83nHT6Nums, 2048),
    (wR8fR83nHT7Labs, wR8fR83nHT7Nums, 2048), (wR8fR83nHT8Labs, wR8fR83nHT8Nums, 2048),
    (wR8fR83nHT9Labs, wR8fR83nHT9Nums, 2048), (wR8fR83nHT10Labs, wR8fR83nHT10Nums, 2048),
    (wR8fR83nHT11Labs, wR8fR83nHT11Nums, 2048), (wR8fR83nHT12Labs, wR8fR83nHT12Nums, 2048),
    (wR8fR83nHT13Labs, wR8fR83nHT13Nums, 2048), (wR8fR83nHT14Labs, wR8fR83nHT14Nums, 2048),
    (wR8fR83nHT15Labs, wR8fR83nHT15Nums, 2048), (wR8fR83nHT16Labs, wR8fR83nHT16Nums, 808)]
    [(wR8fR83nGT0Labs, wR8fR83nGT0Nums, 2048), (wR8fR83nGT1Labs, wR8fR83nGT1Nums, 2048),
    (wR8fR83nGT2Labs, wR8fR83nGT2Nums, 2048), (wR8fR83nGT3Labs, wR8fR83nGT3Nums, 2048),
    (wR8fR83nGT4Labs, wR8fR83nGT4Nums, 2048), (wR8fR83nGT5Labs, wR8fR83nGT5Nums, 2048),
    (wR8fR83nGT6Labs, wR8fR83nGT6Nums, 2048), (wR8fR83nGT7Labs, wR8fR83nGT7Nums, 2048),
    (wR8fR83nGT8Labs, wR8fR83nGT8Nums, 2048), (wR8fR83nGT9Labs, wR8fR83nGT9Nums, 2048),
    (wR8fR83nGT10Labs, wR8fR83nGT10Nums, 2048), (wR8fR83nGT11Labs, wR8fR83nGT11Nums, 2048),
    (wR8fR83nGT12Labs, wR8fR83nGT12Nums, 2048), (wR8fR83nGT13Labs, wR8fR83nGT13Nums, 2048),
    (wR8fR83nGT14Labs, wR8fR83nGT14Nums, 2048), (wR8fR83nGT15Labs, wR8fR83nGT15Nums, 2048),
    (wR8fR83nGT16Labs, wR8fR83nGT16Nums, 2048), (wR8fR83nGT17Labs, wR8fR83nGT17Nums, 2048),
    (wR8fR83nGT18Labs, wR8fR83nGT18Nums, 2048), (wR8fR83nGT19Labs, wR8fR83nGT19Nums, 2048),
    (wR8fR83nGT20Labs, wR8fR83nGT20Nums, 2048), (wR8fR83nGT21Labs, wR8fR83nGT21Nums, 2048),
    (wR8fR83nGT22Labs, wR8fR83nGT22Nums, 1704)] 4029952 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wR8fR83n_Lsh : wR8fR83nL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR83nHT0Labs, wR8fR83nHT0Nums, 2048), (wR8fR83nHT1Labs, wR8fR83nHT1Nums, 2048),
    (wR8fR83nHT2Labs, wR8fR83nHT2Nums, 2048), (wR8fR83nHT3Labs, wR8fR83nHT3Nums, 2048),
    (wR8fR83nHT4Labs, wR8fR83nHT4Nums, 2048), (wR8fR83nHT5Labs, wR8fR83nHT5Nums, 2048),
    (wR8fR83nHT6Labs, wR8fR83nHT6Nums, 2048), (wR8fR83nHT7Labs, wR8fR83nHT7Nums, 2048),
    (wR8fR83nHT8Labs, wR8fR83nHT8Nums, 2048), (wR8fR83nHT9Labs, wR8fR83nHT9Nums, 2048),
    (wR8fR83nHT10Labs, wR8fR83nHT10Nums, 2048), (wR8fR83nHT11Labs, wR8fR83nHT11Nums, 2048),
    (wR8fR83nHT12Labs, wR8fR83nHT12Nums, 2048), (wR8fR83nHT13Labs, wR8fR83nHT13Nums, 2048),
    (wR8fR83nHT14Labs, wR8fR83nHT14Nums, 2048), (wR8fR83nHT15Labs, wR8fR83nHT15Nums, 2048),
    (wR8fR83nHT16Labs, wR8fR83nHT16Nums, 808)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wR8fR83n_Wsh : wR8fR83nW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR83nGT0Labs, wR8fR83nGT0Nums, 2048), (wR8fR83nGT1Labs, wR8fR83nGT1Nums, 2048),
    (wR8fR83nGT2Labs, wR8fR83nGT2Nums, 2048), (wR8fR83nGT3Labs, wR8fR83nGT3Nums, 2048),
    (wR8fR83nGT4Labs, wR8fR83nGT4Nums, 2048), (wR8fR83nGT5Labs, wR8fR83nGT5Nums, 2048),
    (wR8fR83nGT6Labs, wR8fR83nGT6Nums, 2048), (wR8fR83nGT7Labs, wR8fR83nGT7Nums, 2048),
    (wR8fR83nGT8Labs, wR8fR83nGT8Nums, 2048), (wR8fR83nGT9Labs, wR8fR83nGT9Nums, 2048),
    (wR8fR83nGT10Labs, wR8fR83nGT10Nums, 2048), (wR8fR83nGT11Labs, wR8fR83nGT11Nums, 2048),
    (wR8fR83nGT12Labs, wR8fR83nGT12Nums, 2048), (wR8fR83nGT13Labs, wR8fR83nGT13Nums, 2048),
    (wR8fR83nGT14Labs, wR8fR83nGT14Nums, 2048), (wR8fR83nGT15Labs, wR8fR83nGT15Nums, 2048),
    (wR8fR83nGT16Labs, wR8fR83nGT16Nums, 2048), (wR8fR83nGT17Labs, wR8fR83nGT17Nums, 2048),
    (wR8fR83nGT18Labs, wR8fR83nGT18Nums, 2048), (wR8fR83nGT19Labs, wR8fR83nGT19Nums, 2048),
    (wR8fR83nGT20Labs, wR8fR83nGT20Nums, 2048), (wR8fR83nGT21Labs, wR8fR83nGT21Nums, 2048),
    (wR8fR83nGT22Labs, wR8fR83nGT22Nums, 1704)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wR8fR83n_hok : octPackOk 64 wR8fR83nL = true :=
  OctadDense.octPackOk_of_chk 64 6 false wR8fR83nL _ _ 4029952 wR8fR83n_Lsh wR8fR83n_chk

/-- The octad integer sum. -/
theorem wR8fR83n_octn : octSumZ 64 false wR8fR83nL wR8fR83nW = 4029952 :=
  OctadDense.octSumZ_of_chk 64 6 false wR8fR83nL wR8fR83nW _ _ 4029952 wR8fR83n_Lsh wR8fR83n_Wsh
      wR8fR83n_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wR8fR83n_selfchk : OctadDense.selfOctChk 64 [(wR8fR83nGT0Labs, wR8fR83nGT0Nums, 2048),
    (wR8fR83nGT1Labs, wR8fR83nGT1Nums, 2048), (wR8fR83nGT2Labs, wR8fR83nGT2Nums, 2048),
    (wR8fR83nGT3Labs, wR8fR83nGT3Nums, 2048), (wR8fR83nGT4Labs, wR8fR83nGT4Nums, 2048),
    (wR8fR83nGT5Labs, wR8fR83nGT5Nums, 2048), (wR8fR83nGT6Labs, wR8fR83nGT6Nums, 2048),
    (wR8fR83nGT7Labs, wR8fR83nGT7Nums, 2048), (wR8fR83nGT8Labs, wR8fR83nGT8Nums, 2048),
    (wR8fR83nGT9Labs, wR8fR83nGT9Nums, 2048), (wR8fR83nGT10Labs, wR8fR83nGT10Nums, 2048),
    (wR8fR83nGT11Labs, wR8fR83nGT11Nums, 2048), (wR8fR83nGT12Labs, wR8fR83nGT12Nums, 2048),
    (wR8fR83nGT13Labs, wR8fR83nGT13Nums, 2048), (wR8fR83nGT14Labs, wR8fR83nGT14Nums, 2048),
    (wR8fR83nGT15Labs, wR8fR83nGT15Nums, 2048), (wR8fR83nGT16Labs, wR8fR83nGT16Nums, 2048),
    (wR8fR83nGT17Labs, wR8fR83nGT17Nums, 2048), (wR8fR83nGT18Labs, wR8fR83nGT18Nums, 2048),
    (wR8fR83nGT19Labs, wR8fR83nGT19Nums, 2048), (wR8fR83nGT20Labs, wR8fR83nGT20Nums, 2048),
    (wR8fR83nGT21Labs, wR8fR83nGT21Nums, 2048), (wR8fR83nGT22Labs, wR8fR83nGT22Nums, 1704)] 503744
    = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wR8fR83n_hn : wR8fR83nL.sden * (octSumZ 64 false wR8fR83nL wR8fR83nW : ℚ) / 8 =
    wR8fR83nW.sden * (selfOctP wR8fR83nW : ℚ) := by
  rw [wR8fR83n_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wR8fR83nW _ 503744 wR8fR83n_Wsh
      wR8fR83n_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
