/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS7c11nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octads) of the identification Seventh[18]- <-> Tenth[68]- (record
gforest:S7c11-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGoctadXGforestS7c11n_chk : OctadDense.octSumChk 64 7 false
    [(wGoctadXGforestS7c11nHT0Labs, wGoctadXGforestS7c11nHT0Nums, 2048),
    (wGoctadXGforestS7c11nHT1Labs, wGoctadXGforestS7c11nHT1Nums, 2048),
    (wGoctadXGforestS7c11nHT2Labs, wGoctadXGforestS7c11nHT2Nums, 2048),
    (wGoctadXGforestS7c11nHT3Labs, wGoctadXGforestS7c11nHT3Nums, 2048),
    (wGoctadXGforestS7c11nHT4Labs, wGoctadXGforestS7c11nHT4Nums, 2048),
    (wGoctadXGforestS7c11nHT5Labs, wGoctadXGforestS7c11nHT5Nums, 2048),
    (wGoctadXGforestS7c11nHT6Labs, wGoctadXGforestS7c11nHT6Nums, 2048),
    (wGoctadXGforestS7c11nHT7Labs, wGoctadXGforestS7c11nHT7Nums, 2048),
    (wGoctadXGforestS7c11nHT8Labs, wGoctadXGforestS7c11nHT8Nums, 2048),
    (wGoctadXGforestS7c11nHT9Labs, wGoctadXGforestS7c11nHT9Nums, 2048),
    (wGoctadXGforestS7c11nHT10Labs, wGoctadXGforestS7c11nHT10Nums, 2048),
    (wGoctadXGforestS7c11nHT11Labs, wGoctadXGforestS7c11nHT11Nums, 2048),
    (wGoctadXGforestS7c11nHT12Labs, wGoctadXGforestS7c11nHT12Nums, 2048),
    (wGoctadXGforestS7c11nHT13Labs, wGoctadXGforestS7c11nHT13Nums, 1000)]
    [(wGoctadXGforestS7c11nGT0Labs, wGoctadXGforestS7c11nGT0Nums, 2048),
    (wGoctadXGforestS7c11nGT1Labs, wGoctadXGforestS7c11nGT1Nums, 2048),
    (wGoctadXGforestS7c11nGT2Labs, wGoctadXGforestS7c11nGT2Nums, 2048),
    (wGoctadXGforestS7c11nGT3Labs, wGoctadXGforestS7c11nGT3Nums, 2048),
    (wGoctadXGforestS7c11nGT4Labs, wGoctadXGforestS7c11nGT4Nums, 2048),
    (wGoctadXGforestS7c11nGT5Labs, wGoctadXGforestS7c11nGT5Nums, 2048),
    (wGoctadXGforestS7c11nGT6Labs, wGoctadXGforestS7c11nGT6Nums, 2048),
    (wGoctadXGforestS7c11nGT7Labs, wGoctadXGforestS7c11nGT7Nums, 2048),
    (wGoctadXGforestS7c11nGT8Labs, wGoctadXGforestS7c11nGT8Nums, 2048),
    (wGoctadXGforestS7c11nGT9Labs, wGoctadXGforestS7c11nGT9Nums, 2048),
    (wGoctadXGforestS7c11nGT10Labs, wGoctadXGforestS7c11nGT10Nums, 2048),
    (wGoctadXGforestS7c11nGT11Labs, wGoctadXGforestS7c11nGT11Nums, 2048),
    (wGoctadXGforestS7c11nGT12Labs, wGoctadXGforestS7c11nGT12Nums, 2048),
    (wGoctadXGforestS7c11nGT13Labs, wGoctadXGforestS7c11nGT13Nums, 2048),
    (wGoctadXGforestS7c11nGT14Labs, wGoctadXGforestS7c11nGT14Nums, 2048),
    (wGoctadXGforestS7c11nGT15Labs, wGoctadXGforestS7c11nGT15Nums, 2048),
    (wGoctadXGforestS7c11nGT16Labs, wGoctadXGforestS7c11nGT16Nums, 2048),
    (wGoctadXGforestS7c11nGT17Labs, wGoctadXGforestS7c11nGT17Nums, 2048),
    (wGoctadXGforestS7c11nGT18Labs, wGoctadXGforestS7c11nGT18Nums, 2048),
    (wGoctadXGforestS7c11nGT19Labs, wGoctadXGforestS7c11nGT19Nums, 2048),
    (wGoctadXGforestS7c11nGT20Labs, wGoctadXGforestS7c11nGT20Nums, 2048),
    (wGoctadXGforestS7c11nGT21Labs, wGoctadXGforestS7c11nGT21Nums, 2048),
    (wGoctadXGforestS7c11nGT22Labs, wGoctadXGforestS7c11nGT22Nums, 1026)] 1037824 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGoctadXGforestS7c11n_Lsh : wGoctadXGforestS7c11nL.sh = ShortData.ofList
    (OctadDense.octChunkTerms [(wGoctadXGforestS7c11nHT0Labs, wGoctadXGforestS7c11nHT0Nums, 2048),
    (wGoctadXGforestS7c11nHT1Labs, wGoctadXGforestS7c11nHT1Nums, 2048),
    (wGoctadXGforestS7c11nHT2Labs, wGoctadXGforestS7c11nHT2Nums, 2048),
    (wGoctadXGforestS7c11nHT3Labs, wGoctadXGforestS7c11nHT3Nums, 2048),
    (wGoctadXGforestS7c11nHT4Labs, wGoctadXGforestS7c11nHT4Nums, 2048),
    (wGoctadXGforestS7c11nHT5Labs, wGoctadXGforestS7c11nHT5Nums, 2048),
    (wGoctadXGforestS7c11nHT6Labs, wGoctadXGforestS7c11nHT6Nums, 2048),
    (wGoctadXGforestS7c11nHT7Labs, wGoctadXGforestS7c11nHT7Nums, 2048),
    (wGoctadXGforestS7c11nHT8Labs, wGoctadXGforestS7c11nHT8Nums, 2048),
    (wGoctadXGforestS7c11nHT9Labs, wGoctadXGforestS7c11nHT9Nums, 2048),
    (wGoctadXGforestS7c11nHT10Labs, wGoctadXGforestS7c11nHT10Nums, 2048),
    (wGoctadXGforestS7c11nHT11Labs, wGoctadXGforestS7c11nHT11Nums, 2048),
    (wGoctadXGforestS7c11nHT12Labs, wGoctadXGforestS7c11nHT12Nums, 2048),
    (wGoctadXGforestS7c11nHT13Labs, wGoctadXGforestS7c11nHT13Nums, 1000)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGoctadXGforestS7c11n_Wsh : wGoctadXGforestS7c11nW.sh = ShortData.ofList
    (OctadDense.octChunkTerms [(wGoctadXGforestS7c11nGT0Labs, wGoctadXGforestS7c11nGT0Nums, 2048),
    (wGoctadXGforestS7c11nGT1Labs, wGoctadXGforestS7c11nGT1Nums, 2048),
    (wGoctadXGforestS7c11nGT2Labs, wGoctadXGforestS7c11nGT2Nums, 2048),
    (wGoctadXGforestS7c11nGT3Labs, wGoctadXGforestS7c11nGT3Nums, 2048),
    (wGoctadXGforestS7c11nGT4Labs, wGoctadXGforestS7c11nGT4Nums, 2048),
    (wGoctadXGforestS7c11nGT5Labs, wGoctadXGforestS7c11nGT5Nums, 2048),
    (wGoctadXGforestS7c11nGT6Labs, wGoctadXGforestS7c11nGT6Nums, 2048),
    (wGoctadXGforestS7c11nGT7Labs, wGoctadXGforestS7c11nGT7Nums, 2048),
    (wGoctadXGforestS7c11nGT8Labs, wGoctadXGforestS7c11nGT8Nums, 2048),
    (wGoctadXGforestS7c11nGT9Labs, wGoctadXGforestS7c11nGT9Nums, 2048),
    (wGoctadXGforestS7c11nGT10Labs, wGoctadXGforestS7c11nGT10Nums, 2048),
    (wGoctadXGforestS7c11nGT11Labs, wGoctadXGforestS7c11nGT11Nums, 2048),
    (wGoctadXGforestS7c11nGT12Labs, wGoctadXGforestS7c11nGT12Nums, 2048),
    (wGoctadXGforestS7c11nGT13Labs, wGoctadXGforestS7c11nGT13Nums, 2048),
    (wGoctadXGforestS7c11nGT14Labs, wGoctadXGforestS7c11nGT14Nums, 2048),
    (wGoctadXGforestS7c11nGT15Labs, wGoctadXGforestS7c11nGT15Nums, 2048),
    (wGoctadXGforestS7c11nGT16Labs, wGoctadXGforestS7c11nGT16Nums, 2048),
    (wGoctadXGforestS7c11nGT17Labs, wGoctadXGforestS7c11nGT17Nums, 2048),
    (wGoctadXGforestS7c11nGT18Labs, wGoctadXGforestS7c11nGT18Nums, 2048),
    (wGoctadXGforestS7c11nGT19Labs, wGoctadXGforestS7c11nGT19Nums, 2048),
    (wGoctadXGforestS7c11nGT20Labs, wGoctadXGforestS7c11nGT20Nums, 2048),
    (wGoctadXGforestS7c11nGT21Labs, wGoctadXGforestS7c11nGT21Nums, 2048),
    (wGoctadXGforestS7c11nGT22Labs, wGoctadXGforestS7c11nGT22Nums, 1026)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGoctadXGforestS7c11n_hok : octPackOk 64 wGoctadXGforestS7c11nL = true :=
  OctadDense.octPackOk_of_chk 64 7 false wGoctadXGforestS7c11nL _ _ 1037824
      wGoctadXGforestS7c11n_Lsh wGoctadXGforestS7c11n_chk

/-- The octad integer sum. -/
theorem wGoctadXGforestS7c11n_octn : octSumZ 64 false wGoctadXGforestS7c11nL
    wGoctadXGforestS7c11nW = 1037824 :=
  OctadDense.octSumZ_of_chk 64 7 false wGoctadXGforestS7c11nL wGoctadXGforestS7c11nW _ _ 1037824
      wGoctadXGforestS7c11n_Lsh wGoctadXGforestS7c11n_Wsh wGoctadXGforestS7c11n_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGoctadXGforestS7c11n_selfchk : OctadDense.selfOctChk 64 [(wGoctadXGforestS7c11nGT0Labs,
    wGoctadXGforestS7c11nGT0Nums, 2048), (wGoctadXGforestS7c11nGT1Labs,
    wGoctadXGforestS7c11nGT1Nums, 2048), (wGoctadXGforestS7c11nGT2Labs,
    wGoctadXGforestS7c11nGT2Nums, 2048), (wGoctadXGforestS7c11nGT3Labs,
    wGoctadXGforestS7c11nGT3Nums, 2048), (wGoctadXGforestS7c11nGT4Labs,
    wGoctadXGforestS7c11nGT4Nums, 2048), (wGoctadXGforestS7c11nGT5Labs,
    wGoctadXGforestS7c11nGT5Nums, 2048), (wGoctadXGforestS7c11nGT6Labs,
    wGoctadXGforestS7c11nGT6Nums, 2048), (wGoctadXGforestS7c11nGT7Labs,
    wGoctadXGforestS7c11nGT7Nums, 2048), (wGoctadXGforestS7c11nGT8Labs,
    wGoctadXGforestS7c11nGT8Nums, 2048), (wGoctadXGforestS7c11nGT9Labs,
    wGoctadXGforestS7c11nGT9Nums, 2048), (wGoctadXGforestS7c11nGT10Labs,
    wGoctadXGforestS7c11nGT10Nums, 2048), (wGoctadXGforestS7c11nGT11Labs,
    wGoctadXGforestS7c11nGT11Nums, 2048), (wGoctadXGforestS7c11nGT12Labs,
    wGoctadXGforestS7c11nGT12Nums, 2048), (wGoctadXGforestS7c11nGT13Labs,
    wGoctadXGforestS7c11nGT13Nums, 2048), (wGoctadXGforestS7c11nGT14Labs,
    wGoctadXGforestS7c11nGT14Nums, 2048), (wGoctadXGforestS7c11nGT15Labs,
    wGoctadXGforestS7c11nGT15Nums, 2048), (wGoctadXGforestS7c11nGT16Labs,
    wGoctadXGforestS7c11nGT16Nums, 2048), (wGoctadXGforestS7c11nGT17Labs,
    wGoctadXGforestS7c11nGT17Nums, 2048), (wGoctadXGforestS7c11nGT18Labs,
    wGoctadXGforestS7c11nGT18Nums, 2048), (wGoctadXGforestS7c11nGT19Labs,
    wGoctadXGforestS7c11nGT19Nums, 2048), (wGoctadXGforestS7c11nGT20Labs,
    wGoctadXGforestS7c11nGT20Nums, 2048), (wGoctadXGforestS7c11nGT21Labs,
    wGoctadXGforestS7c11nGT21Nums, 2048), (wGoctadXGforestS7c11nGT22Labs,
    wGoctadXGforestS7c11nGT22Nums, 1026)] 518912 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGoctadXGforestS7c11n_hn : wGoctadXGforestS7c11nL.sden * (octSumZ 64 false
    wGoctadXGforestS7c11nL wGoctadXGforestS7c11nW : ℚ) / 8 =
    wGoctadXGforestS7c11nW.sden * (selfOctP wGoctadXGforestS7c11nW : ℚ) := by
  rw [wGoctadXGforestS7c11n_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64
      wGoctadXGforestS7c11nW _ 518912 wGoctadXGforestS7c11n_Wsh wGoctadXGforestS7c11n_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
