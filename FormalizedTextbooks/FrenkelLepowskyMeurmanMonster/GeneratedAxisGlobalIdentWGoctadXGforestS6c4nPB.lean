/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS6c4nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixthF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octads) of the identification Sixth[8]- <-> Tenth[73]+ (record gforest:S6c4-,
e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGoctadXGforestS6c4n_chk : OctadDense.octSumChk 64 6 false [(wGoctadXGforestS6c4nHT0Labs,
    wGoctadXGforestS6c4nHT0Nums, 2048), (wGoctadXGforestS6c4nHT1Labs, wGoctadXGforestS6c4nHT1Nums,
    2048), (wGoctadXGforestS6c4nHT2Labs, wGoctadXGforestS6c4nHT2Nums, 2048),
    (wGoctadXGforestS6c4nHT3Labs, wGoctadXGforestS6c4nHT3Nums, 2048),
    (wGoctadXGforestS6c4nHT4Labs, wGoctadXGforestS6c4nHT4Nums, 2048),
    (wGoctadXGforestS6c4nHT5Labs, wGoctadXGforestS6c4nHT5Nums, 2048),
    (wGoctadXGforestS6c4nHT6Labs, wGoctadXGforestS6c4nHT6Nums, 2048),
    (wGoctadXGforestS6c4nHT7Labs, wGoctadXGforestS6c4nHT7Nums, 2048),
    (wGoctadXGforestS6c4nHT8Labs, wGoctadXGforestS6c4nHT8Nums, 2048),
    (wGoctadXGforestS6c4nHT9Labs, wGoctadXGforestS6c4nHT9Nums, 2048),
    (wGoctadXGforestS6c4nHT10Labs, wGoctadXGforestS6c4nHT10Nums, 2048),
    (wGoctadXGforestS6c4nHT11Labs, wGoctadXGforestS6c4nHT11Nums, 2048),
    (wGoctadXGforestS6c4nHT12Labs, wGoctadXGforestS6c4nHT12Nums, 2048),
    (wGoctadXGforestS6c4nHT13Labs, wGoctadXGforestS6c4nHT13Nums, 2048),
    (wGoctadXGforestS6c4nHT14Labs, wGoctadXGforestS6c4nHT14Nums, 1640)]
    [(wGoctadXGforestS6c4nGT0Labs, wGoctadXGforestS6c4nGT0Nums, 2048),
    (wGoctadXGforestS6c4nGT1Labs, wGoctadXGforestS6c4nGT1Nums, 2048),
    (wGoctadXGforestS6c4nGT2Labs, wGoctadXGforestS6c4nGT2Nums, 2048),
    (wGoctadXGforestS6c4nGT3Labs, wGoctadXGforestS6c4nGT3Nums, 2048),
    (wGoctadXGforestS6c4nGT4Labs, wGoctadXGforestS6c4nGT4Nums, 2048),
    (wGoctadXGforestS6c4nGT5Labs, wGoctadXGforestS6c4nGT5Nums, 2048),
    (wGoctadXGforestS6c4nGT6Labs, wGoctadXGforestS6c4nGT6Nums, 2048),
    (wGoctadXGforestS6c4nGT7Labs, wGoctadXGforestS6c4nGT7Nums, 2048),
    (wGoctadXGforestS6c4nGT8Labs, wGoctadXGforestS6c4nGT8Nums, 2048),
    (wGoctadXGforestS6c4nGT9Labs, wGoctadXGforestS6c4nGT9Nums, 2048),
    (wGoctadXGforestS6c4nGT10Labs, wGoctadXGforestS6c4nGT10Nums, 2048),
    (wGoctadXGforestS6c4nGT11Labs, wGoctadXGforestS6c4nGT11Nums, 2048),
    (wGoctadXGforestS6c4nGT12Labs, wGoctadXGforestS6c4nGT12Nums, 2048),
    (wGoctadXGforestS6c4nGT13Labs, wGoctadXGforestS6c4nGT13Nums, 2048),
    (wGoctadXGforestS6c4nGT14Labs, wGoctadXGforestS6c4nGT14Nums, 2048),
    (wGoctadXGforestS6c4nGT15Labs, wGoctadXGforestS6c4nGT15Nums, 2048),
    (wGoctadXGforestS6c4nGT16Labs, wGoctadXGforestS6c4nGT16Nums, 2048),
    (wGoctadXGforestS6c4nGT17Labs, wGoctadXGforestS6c4nGT17Nums, 2048),
    (wGoctadXGforestS6c4nGT18Labs, wGoctadXGforestS6c4nGT18Nums, 2048),
    (wGoctadXGforestS6c4nGT19Labs, wGoctadXGforestS6c4nGT19Nums, 2048),
    (wGoctadXGforestS6c4nGT20Labs, wGoctadXGforestS6c4nGT20Nums, 2048),
    (wGoctadXGforestS6c4nGT21Labs, wGoctadXGforestS6c4nGT21Nums, 2048),
    (wGoctadXGforestS6c4nGT22Labs, wGoctadXGforestS6c4nGT22Nums, 1026)] 1006976 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGoctadXGforestS6c4n_Lsh : wGoctadXGforestS6c4nL.sh = ShortData.ofList
    (OctadDense.octChunkTerms [(wGoctadXGforestS6c4nHT0Labs, wGoctadXGforestS6c4nHT0Nums, 2048),
    (wGoctadXGforestS6c4nHT1Labs, wGoctadXGforestS6c4nHT1Nums, 2048),
    (wGoctadXGforestS6c4nHT2Labs, wGoctadXGforestS6c4nHT2Nums, 2048),
    (wGoctadXGforestS6c4nHT3Labs, wGoctadXGforestS6c4nHT3Nums, 2048),
    (wGoctadXGforestS6c4nHT4Labs, wGoctadXGforestS6c4nHT4Nums, 2048),
    (wGoctadXGforestS6c4nHT5Labs, wGoctadXGforestS6c4nHT5Nums, 2048),
    (wGoctadXGforestS6c4nHT6Labs, wGoctadXGforestS6c4nHT6Nums, 2048),
    (wGoctadXGforestS6c4nHT7Labs, wGoctadXGforestS6c4nHT7Nums, 2048),
    (wGoctadXGforestS6c4nHT8Labs, wGoctadXGforestS6c4nHT8Nums, 2048),
    (wGoctadXGforestS6c4nHT9Labs, wGoctadXGforestS6c4nHT9Nums, 2048),
    (wGoctadXGforestS6c4nHT10Labs, wGoctadXGforestS6c4nHT10Nums, 2048),
    (wGoctadXGforestS6c4nHT11Labs, wGoctadXGforestS6c4nHT11Nums, 2048),
    (wGoctadXGforestS6c4nHT12Labs, wGoctadXGforestS6c4nHT12Nums, 2048),
    (wGoctadXGforestS6c4nHT13Labs, wGoctadXGforestS6c4nHT13Nums, 2048),
    (wGoctadXGforestS6c4nHT14Labs, wGoctadXGforestS6c4nHT14Nums, 1640)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGoctadXGforestS6c4n_Wsh : wGoctadXGforestS6c4nW.sh = ShortData.ofList
    (OctadDense.octChunkTerms [(wGoctadXGforestS6c4nGT0Labs, wGoctadXGforestS6c4nGT0Nums, 2048),
    (wGoctadXGforestS6c4nGT1Labs, wGoctadXGforestS6c4nGT1Nums, 2048),
    (wGoctadXGforestS6c4nGT2Labs, wGoctadXGforestS6c4nGT2Nums, 2048),
    (wGoctadXGforestS6c4nGT3Labs, wGoctadXGforestS6c4nGT3Nums, 2048),
    (wGoctadXGforestS6c4nGT4Labs, wGoctadXGforestS6c4nGT4Nums, 2048),
    (wGoctadXGforestS6c4nGT5Labs, wGoctadXGforestS6c4nGT5Nums, 2048),
    (wGoctadXGforestS6c4nGT6Labs, wGoctadXGforestS6c4nGT6Nums, 2048),
    (wGoctadXGforestS6c4nGT7Labs, wGoctadXGforestS6c4nGT7Nums, 2048),
    (wGoctadXGforestS6c4nGT8Labs, wGoctadXGforestS6c4nGT8Nums, 2048),
    (wGoctadXGforestS6c4nGT9Labs, wGoctadXGforestS6c4nGT9Nums, 2048),
    (wGoctadXGforestS6c4nGT10Labs, wGoctadXGforestS6c4nGT10Nums, 2048),
    (wGoctadXGforestS6c4nGT11Labs, wGoctadXGforestS6c4nGT11Nums, 2048),
    (wGoctadXGforestS6c4nGT12Labs, wGoctadXGforestS6c4nGT12Nums, 2048),
    (wGoctadXGforestS6c4nGT13Labs, wGoctadXGforestS6c4nGT13Nums, 2048),
    (wGoctadXGforestS6c4nGT14Labs, wGoctadXGforestS6c4nGT14Nums, 2048),
    (wGoctadXGforestS6c4nGT15Labs, wGoctadXGforestS6c4nGT15Nums, 2048),
    (wGoctadXGforestS6c4nGT16Labs, wGoctadXGforestS6c4nGT16Nums, 2048),
    (wGoctadXGforestS6c4nGT17Labs, wGoctadXGforestS6c4nGT17Nums, 2048),
    (wGoctadXGforestS6c4nGT18Labs, wGoctadXGforestS6c4nGT18Nums, 2048),
    (wGoctadXGforestS6c4nGT19Labs, wGoctadXGforestS6c4nGT19Nums, 2048),
    (wGoctadXGforestS6c4nGT20Labs, wGoctadXGforestS6c4nGT20Nums, 2048),
    (wGoctadXGforestS6c4nGT21Labs, wGoctadXGforestS6c4nGT21Nums, 2048),
    (wGoctadXGforestS6c4nGT22Labs, wGoctadXGforestS6c4nGT22Nums, 1026)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGoctadXGforestS6c4n_hok : octPackOk 64 wGoctadXGforestS6c4nL = true :=
  OctadDense.octPackOk_of_chk 64 6 false wGoctadXGforestS6c4nL _ _ 1006976
      wGoctadXGforestS6c4n_Lsh wGoctadXGforestS6c4n_chk

/-- The octad integer sum. -/
theorem wGoctadXGforestS6c4n_octn : octSumZ 64 false wGoctadXGforestS6c4nL wGoctadXGforestS6c4nW =
    1006976 :=
  OctadDense.octSumZ_of_chk 64 6 false wGoctadXGforestS6c4nL wGoctadXGforestS6c4nW _ _ 1006976
      wGoctadXGforestS6c4n_Lsh wGoctadXGforestS6c4n_Wsh wGoctadXGforestS6c4n_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGoctadXGforestS6c4n_selfchk : OctadDense.selfOctChk 64 [(wGoctadXGforestS6c4nGT0Labs,
    wGoctadXGforestS6c4nGT0Nums, 2048), (wGoctadXGforestS6c4nGT1Labs, wGoctadXGforestS6c4nGT1Nums,
    2048), (wGoctadXGforestS6c4nGT2Labs, wGoctadXGforestS6c4nGT2Nums, 2048),
    (wGoctadXGforestS6c4nGT3Labs, wGoctadXGforestS6c4nGT3Nums, 2048),
    (wGoctadXGforestS6c4nGT4Labs, wGoctadXGforestS6c4nGT4Nums, 2048),
    (wGoctadXGforestS6c4nGT5Labs, wGoctadXGforestS6c4nGT5Nums, 2048),
    (wGoctadXGforestS6c4nGT6Labs, wGoctadXGforestS6c4nGT6Nums, 2048),
    (wGoctadXGforestS6c4nGT7Labs, wGoctadXGforestS6c4nGT7Nums, 2048),
    (wGoctadXGforestS6c4nGT8Labs, wGoctadXGforestS6c4nGT8Nums, 2048),
    (wGoctadXGforestS6c4nGT9Labs, wGoctadXGforestS6c4nGT9Nums, 2048),
    (wGoctadXGforestS6c4nGT10Labs, wGoctadXGforestS6c4nGT10Nums, 2048),
    (wGoctadXGforestS6c4nGT11Labs, wGoctadXGforestS6c4nGT11Nums, 2048),
    (wGoctadXGforestS6c4nGT12Labs, wGoctadXGforestS6c4nGT12Nums, 2048),
    (wGoctadXGforestS6c4nGT13Labs, wGoctadXGforestS6c4nGT13Nums, 2048),
    (wGoctadXGforestS6c4nGT14Labs, wGoctadXGforestS6c4nGT14Nums, 2048),
    (wGoctadXGforestS6c4nGT15Labs, wGoctadXGforestS6c4nGT15Nums, 2048),
    (wGoctadXGforestS6c4nGT16Labs, wGoctadXGforestS6c4nGT16Nums, 2048),
    (wGoctadXGforestS6c4nGT17Labs, wGoctadXGforestS6c4nGT17Nums, 2048),
    (wGoctadXGforestS6c4nGT18Labs, wGoctadXGforestS6c4nGT18Nums, 2048),
    (wGoctadXGforestS6c4nGT19Labs, wGoctadXGforestS6c4nGT19Nums, 2048),
    (wGoctadXGforestS6c4nGT20Labs, wGoctadXGforestS6c4nGT20Nums, 2048),
    (wGoctadXGforestS6c4nGT21Labs, wGoctadXGforestS6c4nGT21Nums, 2048),
    (wGoctadXGforestS6c4nGT22Labs, wGoctadXGforestS6c4nGT22Nums, 1026)] 503488 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGoctadXGforestS6c4n_hn : wGoctadXGforestS6c4nL.sden * (octSumZ 64 false
    wGoctadXGforestS6c4nL wGoctadXGforestS6c4nW : ℚ) / 8 =
    wGoctadXGforestS6c4nW.sden * (selfOctP wGoctadXGforestS6c4nW : ℚ) := by
  rw [wGoctadXGforestS6c4n_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGoctadXGforestS6c4nW
      _ 503488 wGoctadXGforestS6c4n_Wsh wGoctadXGforestS6c4n_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
