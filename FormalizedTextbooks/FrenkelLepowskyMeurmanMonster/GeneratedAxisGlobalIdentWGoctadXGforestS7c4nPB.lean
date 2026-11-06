/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS7c4nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octads) of the identification Seventh[9]- <-> Tenth[1]+ (record
gforest:S7c4-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGoctadXGforestS7c4n_chk : OctadDense.octSumChk 64 7 false [(wGoctadXGforestS7c4nHT0Labs,
    wGoctadXGforestS7c4nHT0Nums, 2048), (wGoctadXGforestS7c4nHT1Labs, wGoctadXGforestS7c4nHT1Nums,
    2048), (wGoctadXGforestS7c4nHT2Labs, wGoctadXGforestS7c4nHT2Nums, 2048),
    (wGoctadXGforestS7c4nHT3Labs, wGoctadXGforestS7c4nHT3Nums, 2048),
    (wGoctadXGforestS7c4nHT4Labs, wGoctadXGforestS7c4nHT4Nums, 2048),
    (wGoctadXGforestS7c4nHT5Labs, wGoctadXGforestS7c4nHT5Nums, 2048),
    (wGoctadXGforestS7c4nHT6Labs, wGoctadXGforestS7c4nHT6Nums, 2048),
    (wGoctadXGforestS7c4nHT7Labs, wGoctadXGforestS7c4nHT7Nums, 2048),
    (wGoctadXGforestS7c4nHT8Labs, wGoctadXGforestS7c4nHT8Nums, 2048),
    (wGoctadXGforestS7c4nHT9Labs, wGoctadXGforestS7c4nHT9Nums, 2048),
    (wGoctadXGforestS7c4nHT10Labs, wGoctadXGforestS7c4nHT10Nums, 2048),
    (wGoctadXGforestS7c4nHT11Labs, wGoctadXGforestS7c4nHT11Nums, 2048),
    (wGoctadXGforestS7c4nHT12Labs, wGoctadXGforestS7c4nHT12Nums, 2048),
    (wGoctadXGforestS7c4nHT13Labs, wGoctadXGforestS7c4nHT13Nums, 1000)]
    [(wGoctadXGforestS7c4nGT0Labs, wGoctadXGforestS7c4nGT0Nums, 2048),
    (wGoctadXGforestS7c4nGT1Labs, wGoctadXGforestS7c4nGT1Nums, 2048),
    (wGoctadXGforestS7c4nGT2Labs, wGoctadXGforestS7c4nGT2Nums, 2048),
    (wGoctadXGforestS7c4nGT3Labs, wGoctadXGforestS7c4nGT3Nums, 2048),
    (wGoctadXGforestS7c4nGT4Labs, wGoctadXGforestS7c4nGT4Nums, 2048),
    (wGoctadXGforestS7c4nGT5Labs, wGoctadXGforestS7c4nGT5Nums, 2048),
    (wGoctadXGforestS7c4nGT6Labs, wGoctadXGforestS7c4nGT6Nums, 2048),
    (wGoctadXGforestS7c4nGT7Labs, wGoctadXGforestS7c4nGT7Nums, 2048),
    (wGoctadXGforestS7c4nGT8Labs, wGoctadXGforestS7c4nGT8Nums, 2048),
    (wGoctadXGforestS7c4nGT9Labs, wGoctadXGforestS7c4nGT9Nums, 2048),
    (wGoctadXGforestS7c4nGT10Labs, wGoctadXGforestS7c4nGT10Nums, 2048),
    (wGoctadXGforestS7c4nGT11Labs, wGoctadXGforestS7c4nGT11Nums, 2048),
    (wGoctadXGforestS7c4nGT12Labs, wGoctadXGforestS7c4nGT12Nums, 2048),
    (wGoctadXGforestS7c4nGT13Labs, wGoctadXGforestS7c4nGT13Nums, 2048),
    (wGoctadXGforestS7c4nGT14Labs, wGoctadXGforestS7c4nGT14Nums, 2048),
    (wGoctadXGforestS7c4nGT15Labs, wGoctadXGforestS7c4nGT15Nums, 2048),
    (wGoctadXGforestS7c4nGT16Labs, wGoctadXGforestS7c4nGT16Nums, 2048),
    (wGoctadXGforestS7c4nGT17Labs, wGoctadXGforestS7c4nGT17Nums, 2048),
    (wGoctadXGforestS7c4nGT18Labs, wGoctadXGforestS7c4nGT18Nums, 2048),
    (wGoctadXGforestS7c4nGT19Labs, wGoctadXGforestS7c4nGT19Nums, 2048),
    (wGoctadXGforestS7c4nGT20Labs, wGoctadXGforestS7c4nGT20Nums, 2048),
    (wGoctadXGforestS7c4nGT21Labs, wGoctadXGforestS7c4nGT21Nums, 2048),
    (wGoctadXGforestS7c4nGT22Labs, wGoctadXGforestS7c4nGT22Nums, 1026)] 1033600 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGoctadXGforestS7c4n_Lsh : wGoctadXGforestS7c4nL.sh = ShortData.ofList
    (OctadDense.octChunkTerms [(wGoctadXGforestS7c4nHT0Labs, wGoctadXGforestS7c4nHT0Nums, 2048),
    (wGoctadXGforestS7c4nHT1Labs, wGoctadXGforestS7c4nHT1Nums, 2048),
    (wGoctadXGforestS7c4nHT2Labs, wGoctadXGforestS7c4nHT2Nums, 2048),
    (wGoctadXGforestS7c4nHT3Labs, wGoctadXGforestS7c4nHT3Nums, 2048),
    (wGoctadXGforestS7c4nHT4Labs, wGoctadXGforestS7c4nHT4Nums, 2048),
    (wGoctadXGforestS7c4nHT5Labs, wGoctadXGforestS7c4nHT5Nums, 2048),
    (wGoctadXGforestS7c4nHT6Labs, wGoctadXGforestS7c4nHT6Nums, 2048),
    (wGoctadXGforestS7c4nHT7Labs, wGoctadXGforestS7c4nHT7Nums, 2048),
    (wGoctadXGforestS7c4nHT8Labs, wGoctadXGforestS7c4nHT8Nums, 2048),
    (wGoctadXGforestS7c4nHT9Labs, wGoctadXGforestS7c4nHT9Nums, 2048),
    (wGoctadXGforestS7c4nHT10Labs, wGoctadXGforestS7c4nHT10Nums, 2048),
    (wGoctadXGforestS7c4nHT11Labs, wGoctadXGforestS7c4nHT11Nums, 2048),
    (wGoctadXGforestS7c4nHT12Labs, wGoctadXGforestS7c4nHT12Nums, 2048),
    (wGoctadXGforestS7c4nHT13Labs, wGoctadXGforestS7c4nHT13Nums, 1000)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGoctadXGforestS7c4n_Wsh : wGoctadXGforestS7c4nW.sh = ShortData.ofList
    (OctadDense.octChunkTerms [(wGoctadXGforestS7c4nGT0Labs, wGoctadXGforestS7c4nGT0Nums, 2048),
    (wGoctadXGforestS7c4nGT1Labs, wGoctadXGforestS7c4nGT1Nums, 2048),
    (wGoctadXGforestS7c4nGT2Labs, wGoctadXGforestS7c4nGT2Nums, 2048),
    (wGoctadXGforestS7c4nGT3Labs, wGoctadXGforestS7c4nGT3Nums, 2048),
    (wGoctadXGforestS7c4nGT4Labs, wGoctadXGforestS7c4nGT4Nums, 2048),
    (wGoctadXGforestS7c4nGT5Labs, wGoctadXGforestS7c4nGT5Nums, 2048),
    (wGoctadXGforestS7c4nGT6Labs, wGoctadXGforestS7c4nGT6Nums, 2048),
    (wGoctadXGforestS7c4nGT7Labs, wGoctadXGforestS7c4nGT7Nums, 2048),
    (wGoctadXGforestS7c4nGT8Labs, wGoctadXGforestS7c4nGT8Nums, 2048),
    (wGoctadXGforestS7c4nGT9Labs, wGoctadXGforestS7c4nGT9Nums, 2048),
    (wGoctadXGforestS7c4nGT10Labs, wGoctadXGforestS7c4nGT10Nums, 2048),
    (wGoctadXGforestS7c4nGT11Labs, wGoctadXGforestS7c4nGT11Nums, 2048),
    (wGoctadXGforestS7c4nGT12Labs, wGoctadXGforestS7c4nGT12Nums, 2048),
    (wGoctadXGforestS7c4nGT13Labs, wGoctadXGforestS7c4nGT13Nums, 2048),
    (wGoctadXGforestS7c4nGT14Labs, wGoctadXGforestS7c4nGT14Nums, 2048),
    (wGoctadXGforestS7c4nGT15Labs, wGoctadXGforestS7c4nGT15Nums, 2048),
    (wGoctadXGforestS7c4nGT16Labs, wGoctadXGforestS7c4nGT16Nums, 2048),
    (wGoctadXGforestS7c4nGT17Labs, wGoctadXGforestS7c4nGT17Nums, 2048),
    (wGoctadXGforestS7c4nGT18Labs, wGoctadXGforestS7c4nGT18Nums, 2048),
    (wGoctadXGforestS7c4nGT19Labs, wGoctadXGforestS7c4nGT19Nums, 2048),
    (wGoctadXGforestS7c4nGT20Labs, wGoctadXGforestS7c4nGT20Nums, 2048),
    (wGoctadXGforestS7c4nGT21Labs, wGoctadXGforestS7c4nGT21Nums, 2048),
    (wGoctadXGforestS7c4nGT22Labs, wGoctadXGforestS7c4nGT22Nums, 1026)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGoctadXGforestS7c4n_hok : octPackOk 64 wGoctadXGforestS7c4nL = true :=
  OctadDense.octPackOk_of_chk 64 7 false wGoctadXGforestS7c4nL _ _ 1033600
      wGoctadXGforestS7c4n_Lsh wGoctadXGforestS7c4n_chk

/-- The octad integer sum. -/
theorem wGoctadXGforestS7c4n_octn : octSumZ 64 false wGoctadXGforestS7c4nL wGoctadXGforestS7c4nW =
    1033600 :=
  OctadDense.octSumZ_of_chk 64 7 false wGoctadXGforestS7c4nL wGoctadXGforestS7c4nW _ _ 1033600
      wGoctadXGforestS7c4n_Lsh wGoctadXGforestS7c4n_Wsh wGoctadXGforestS7c4n_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGoctadXGforestS7c4n_selfchk : OctadDense.selfOctChk 64 [(wGoctadXGforestS7c4nGT0Labs,
    wGoctadXGforestS7c4nGT0Nums, 2048), (wGoctadXGforestS7c4nGT1Labs, wGoctadXGforestS7c4nGT1Nums,
    2048), (wGoctadXGforestS7c4nGT2Labs, wGoctadXGforestS7c4nGT2Nums, 2048),
    (wGoctadXGforestS7c4nGT3Labs, wGoctadXGforestS7c4nGT3Nums, 2048),
    (wGoctadXGforestS7c4nGT4Labs, wGoctadXGforestS7c4nGT4Nums, 2048),
    (wGoctadXGforestS7c4nGT5Labs, wGoctadXGforestS7c4nGT5Nums, 2048),
    (wGoctadXGforestS7c4nGT6Labs, wGoctadXGforestS7c4nGT6Nums, 2048),
    (wGoctadXGforestS7c4nGT7Labs, wGoctadXGforestS7c4nGT7Nums, 2048),
    (wGoctadXGforestS7c4nGT8Labs, wGoctadXGforestS7c4nGT8Nums, 2048),
    (wGoctadXGforestS7c4nGT9Labs, wGoctadXGforestS7c4nGT9Nums, 2048),
    (wGoctadXGforestS7c4nGT10Labs, wGoctadXGforestS7c4nGT10Nums, 2048),
    (wGoctadXGforestS7c4nGT11Labs, wGoctadXGforestS7c4nGT11Nums, 2048),
    (wGoctadXGforestS7c4nGT12Labs, wGoctadXGforestS7c4nGT12Nums, 2048),
    (wGoctadXGforestS7c4nGT13Labs, wGoctadXGforestS7c4nGT13Nums, 2048),
    (wGoctadXGforestS7c4nGT14Labs, wGoctadXGforestS7c4nGT14Nums, 2048),
    (wGoctadXGforestS7c4nGT15Labs, wGoctadXGforestS7c4nGT15Nums, 2048),
    (wGoctadXGforestS7c4nGT16Labs, wGoctadXGforestS7c4nGT16Nums, 2048),
    (wGoctadXGforestS7c4nGT17Labs, wGoctadXGforestS7c4nGT17Nums, 2048),
    (wGoctadXGforestS7c4nGT18Labs, wGoctadXGforestS7c4nGT18Nums, 2048),
    (wGoctadXGforestS7c4nGT19Labs, wGoctadXGforestS7c4nGT19Nums, 2048),
    (wGoctadXGforestS7c4nGT20Labs, wGoctadXGforestS7c4nGT20Nums, 2048),
    (wGoctadXGforestS7c4nGT21Labs, wGoctadXGforestS7c4nGT21Nums, 2048),
    (wGoctadXGforestS7c4nGT22Labs, wGoctadXGforestS7c4nGT22Nums, 1026)] 516800 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGoctadXGforestS7c4n_hn : wGoctadXGforestS7c4nL.sden * (octSumZ 64 false
    wGoctadXGforestS7c4nL wGoctadXGforestS7c4nW : ℚ) / 8 =
    wGoctadXGforestS7c4nW.sden * (selfOctP wGoctadXGforestS7c4nW : ℚ) := by
  rw [wGoctadXGforestS7c4n_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGoctadXGforestS7c4nW
      _ 516800 wGoctadXGforestS7c4n_Wsh wGoctadXGforestS7c4n_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
