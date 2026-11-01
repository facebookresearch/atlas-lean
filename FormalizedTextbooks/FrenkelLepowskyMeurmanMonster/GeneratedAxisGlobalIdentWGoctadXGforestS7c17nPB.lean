/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS7c17nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octads) of the identification Seventh[26]- <-> Tenth[66]+ (record
gforest:S7c17-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGoctadXGforestS7c17n_chk : OctadDense.octSumChk 64 7 false
    [(wGoctadXGforestS7c17nHT0Labs, wGoctadXGforestS7c17nHT0Nums, 2048),
    (wGoctadXGforestS7c17nHT1Labs, wGoctadXGforestS7c17nHT1Nums, 2048),
    (wGoctadXGforestS7c17nHT2Labs, wGoctadXGforestS7c17nHT2Nums, 2048),
    (wGoctadXGforestS7c17nHT3Labs, wGoctadXGforestS7c17nHT3Nums, 2048),
    (wGoctadXGforestS7c17nHT4Labs, wGoctadXGforestS7c17nHT4Nums, 2048),
    (wGoctadXGforestS7c17nHT5Labs, wGoctadXGforestS7c17nHT5Nums, 2048),
    (wGoctadXGforestS7c17nHT6Labs, wGoctadXGforestS7c17nHT6Nums, 2048),
    (wGoctadXGforestS7c17nHT7Labs, wGoctadXGforestS7c17nHT7Nums, 2048),
    (wGoctadXGforestS7c17nHT8Labs, wGoctadXGforestS7c17nHT8Nums, 2048),
    (wGoctadXGforestS7c17nHT9Labs, wGoctadXGforestS7c17nHT9Nums, 2048),
    (wGoctadXGforestS7c17nHT10Labs, wGoctadXGforestS7c17nHT10Nums, 2048),
    (wGoctadXGforestS7c17nHT11Labs, wGoctadXGforestS7c17nHT11Nums, 2048),
    (wGoctadXGforestS7c17nHT12Labs, wGoctadXGforestS7c17nHT12Nums, 2048),
    (wGoctadXGforestS7c17nHT13Labs, wGoctadXGforestS7c17nHT13Nums, 1000)]
    [(wGoctadXGforestS7c17nGT0Labs, wGoctadXGforestS7c17nGT0Nums, 2048),
    (wGoctadXGforestS7c17nGT1Labs, wGoctadXGforestS7c17nGT1Nums, 2048),
    (wGoctadXGforestS7c17nGT2Labs, wGoctadXGforestS7c17nGT2Nums, 2048),
    (wGoctadXGforestS7c17nGT3Labs, wGoctadXGforestS7c17nGT3Nums, 2048),
    (wGoctadXGforestS7c17nGT4Labs, wGoctadXGforestS7c17nGT4Nums, 2048),
    (wGoctadXGforestS7c17nGT5Labs, wGoctadXGforestS7c17nGT5Nums, 2048),
    (wGoctadXGforestS7c17nGT6Labs, wGoctadXGforestS7c17nGT6Nums, 2048),
    (wGoctadXGforestS7c17nGT7Labs, wGoctadXGforestS7c17nGT7Nums, 2048),
    (wGoctadXGforestS7c17nGT8Labs, wGoctadXGforestS7c17nGT8Nums, 2048),
    (wGoctadXGforestS7c17nGT9Labs, wGoctadXGforestS7c17nGT9Nums, 2048),
    (wGoctadXGforestS7c17nGT10Labs, wGoctadXGforestS7c17nGT10Nums, 2048),
    (wGoctadXGforestS7c17nGT11Labs, wGoctadXGforestS7c17nGT11Nums, 2048),
    (wGoctadXGforestS7c17nGT12Labs, wGoctadXGforestS7c17nGT12Nums, 2048),
    (wGoctadXGforestS7c17nGT13Labs, wGoctadXGforestS7c17nGT13Nums, 2048),
    (wGoctadXGforestS7c17nGT14Labs, wGoctadXGforestS7c17nGT14Nums, 2048),
    (wGoctadXGforestS7c17nGT15Labs, wGoctadXGforestS7c17nGT15Nums, 2048),
    (wGoctadXGforestS7c17nGT16Labs, wGoctadXGforestS7c17nGT16Nums, 2048),
    (wGoctadXGforestS7c17nGT17Labs, wGoctadXGforestS7c17nGT17Nums, 2048),
    (wGoctadXGforestS7c17nGT18Labs, wGoctadXGforestS7c17nGT18Nums, 2048),
    (wGoctadXGforestS7c17nGT19Labs, wGoctadXGforestS7c17nGT19Nums, 2048),
    (wGoctadXGforestS7c17nGT20Labs, wGoctadXGforestS7c17nGT20Nums, 2048),
    (wGoctadXGforestS7c17nGT21Labs, wGoctadXGforestS7c17nGT21Nums, 2048),
    (wGoctadXGforestS7c17nGT22Labs, wGoctadXGforestS7c17nGT22Nums, 1026)] 1043456 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGoctadXGforestS7c17n_Lsh : wGoctadXGforestS7c17nL.sh = ShortData.ofList
    (OctadDense.octChunkTerms [(wGoctadXGforestS7c17nHT0Labs, wGoctadXGforestS7c17nHT0Nums, 2048),
    (wGoctadXGforestS7c17nHT1Labs, wGoctadXGforestS7c17nHT1Nums, 2048),
    (wGoctadXGforestS7c17nHT2Labs, wGoctadXGforestS7c17nHT2Nums, 2048),
    (wGoctadXGforestS7c17nHT3Labs, wGoctadXGforestS7c17nHT3Nums, 2048),
    (wGoctadXGforestS7c17nHT4Labs, wGoctadXGforestS7c17nHT4Nums, 2048),
    (wGoctadXGforestS7c17nHT5Labs, wGoctadXGforestS7c17nHT5Nums, 2048),
    (wGoctadXGforestS7c17nHT6Labs, wGoctadXGforestS7c17nHT6Nums, 2048),
    (wGoctadXGforestS7c17nHT7Labs, wGoctadXGforestS7c17nHT7Nums, 2048),
    (wGoctadXGforestS7c17nHT8Labs, wGoctadXGforestS7c17nHT8Nums, 2048),
    (wGoctadXGforestS7c17nHT9Labs, wGoctadXGforestS7c17nHT9Nums, 2048),
    (wGoctadXGforestS7c17nHT10Labs, wGoctadXGforestS7c17nHT10Nums, 2048),
    (wGoctadXGforestS7c17nHT11Labs, wGoctadXGforestS7c17nHT11Nums, 2048),
    (wGoctadXGforestS7c17nHT12Labs, wGoctadXGforestS7c17nHT12Nums, 2048),
    (wGoctadXGforestS7c17nHT13Labs, wGoctadXGforestS7c17nHT13Nums, 1000)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGoctadXGforestS7c17n_Wsh : wGoctadXGforestS7c17nW.sh = ShortData.ofList
    (OctadDense.octChunkTerms [(wGoctadXGforestS7c17nGT0Labs, wGoctadXGforestS7c17nGT0Nums, 2048),
    (wGoctadXGforestS7c17nGT1Labs, wGoctadXGforestS7c17nGT1Nums, 2048),
    (wGoctadXGforestS7c17nGT2Labs, wGoctadXGforestS7c17nGT2Nums, 2048),
    (wGoctadXGforestS7c17nGT3Labs, wGoctadXGforestS7c17nGT3Nums, 2048),
    (wGoctadXGforestS7c17nGT4Labs, wGoctadXGforestS7c17nGT4Nums, 2048),
    (wGoctadXGforestS7c17nGT5Labs, wGoctadXGforestS7c17nGT5Nums, 2048),
    (wGoctadXGforestS7c17nGT6Labs, wGoctadXGforestS7c17nGT6Nums, 2048),
    (wGoctadXGforestS7c17nGT7Labs, wGoctadXGforestS7c17nGT7Nums, 2048),
    (wGoctadXGforestS7c17nGT8Labs, wGoctadXGforestS7c17nGT8Nums, 2048),
    (wGoctadXGforestS7c17nGT9Labs, wGoctadXGforestS7c17nGT9Nums, 2048),
    (wGoctadXGforestS7c17nGT10Labs, wGoctadXGforestS7c17nGT10Nums, 2048),
    (wGoctadXGforestS7c17nGT11Labs, wGoctadXGforestS7c17nGT11Nums, 2048),
    (wGoctadXGforestS7c17nGT12Labs, wGoctadXGforestS7c17nGT12Nums, 2048),
    (wGoctadXGforestS7c17nGT13Labs, wGoctadXGforestS7c17nGT13Nums, 2048),
    (wGoctadXGforestS7c17nGT14Labs, wGoctadXGforestS7c17nGT14Nums, 2048),
    (wGoctadXGforestS7c17nGT15Labs, wGoctadXGforestS7c17nGT15Nums, 2048),
    (wGoctadXGforestS7c17nGT16Labs, wGoctadXGforestS7c17nGT16Nums, 2048),
    (wGoctadXGforestS7c17nGT17Labs, wGoctadXGforestS7c17nGT17Nums, 2048),
    (wGoctadXGforestS7c17nGT18Labs, wGoctadXGforestS7c17nGT18Nums, 2048),
    (wGoctadXGforestS7c17nGT19Labs, wGoctadXGforestS7c17nGT19Nums, 2048),
    (wGoctadXGforestS7c17nGT20Labs, wGoctadXGforestS7c17nGT20Nums, 2048),
    (wGoctadXGforestS7c17nGT21Labs, wGoctadXGforestS7c17nGT21Nums, 2048),
    (wGoctadXGforestS7c17nGT22Labs, wGoctadXGforestS7c17nGT22Nums, 1026)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGoctadXGforestS7c17n_hok : octPackOk 64 wGoctadXGforestS7c17nL = true :=
  OctadDense.octPackOk_of_chk 64 7 false wGoctadXGforestS7c17nL _ _ 1043456
      wGoctadXGforestS7c17n_Lsh wGoctadXGforestS7c17n_chk

/-- The octad integer sum. -/
theorem wGoctadXGforestS7c17n_octn : octSumZ 64 false wGoctadXGforestS7c17nL
    wGoctadXGforestS7c17nW = 1043456 :=
  OctadDense.octSumZ_of_chk 64 7 false wGoctadXGforestS7c17nL wGoctadXGforestS7c17nW _ _ 1043456
      wGoctadXGforestS7c17n_Lsh wGoctadXGforestS7c17n_Wsh wGoctadXGforestS7c17n_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGoctadXGforestS7c17n_selfchk : OctadDense.selfOctChk 64 [(wGoctadXGforestS7c17nGT0Labs,
    wGoctadXGforestS7c17nGT0Nums, 2048), (wGoctadXGforestS7c17nGT1Labs,
    wGoctadXGforestS7c17nGT1Nums, 2048), (wGoctadXGforestS7c17nGT2Labs,
    wGoctadXGforestS7c17nGT2Nums, 2048), (wGoctadXGforestS7c17nGT3Labs,
    wGoctadXGforestS7c17nGT3Nums, 2048), (wGoctadXGforestS7c17nGT4Labs,
    wGoctadXGforestS7c17nGT4Nums, 2048), (wGoctadXGforestS7c17nGT5Labs,
    wGoctadXGforestS7c17nGT5Nums, 2048), (wGoctadXGforestS7c17nGT6Labs,
    wGoctadXGforestS7c17nGT6Nums, 2048), (wGoctadXGforestS7c17nGT7Labs,
    wGoctadXGforestS7c17nGT7Nums, 2048), (wGoctadXGforestS7c17nGT8Labs,
    wGoctadXGforestS7c17nGT8Nums, 2048), (wGoctadXGforestS7c17nGT9Labs,
    wGoctadXGforestS7c17nGT9Nums, 2048), (wGoctadXGforestS7c17nGT10Labs,
    wGoctadXGforestS7c17nGT10Nums, 2048), (wGoctadXGforestS7c17nGT11Labs,
    wGoctadXGforestS7c17nGT11Nums, 2048), (wGoctadXGforestS7c17nGT12Labs,
    wGoctadXGforestS7c17nGT12Nums, 2048), (wGoctadXGforestS7c17nGT13Labs,
    wGoctadXGforestS7c17nGT13Nums, 2048), (wGoctadXGforestS7c17nGT14Labs,
    wGoctadXGforestS7c17nGT14Nums, 2048), (wGoctadXGforestS7c17nGT15Labs,
    wGoctadXGforestS7c17nGT15Nums, 2048), (wGoctadXGforestS7c17nGT16Labs,
    wGoctadXGforestS7c17nGT16Nums, 2048), (wGoctadXGforestS7c17nGT17Labs,
    wGoctadXGforestS7c17nGT17Nums, 2048), (wGoctadXGforestS7c17nGT18Labs,
    wGoctadXGforestS7c17nGT18Nums, 2048), (wGoctadXGforestS7c17nGT19Labs,
    wGoctadXGforestS7c17nGT19Nums, 2048), (wGoctadXGforestS7c17nGT20Labs,
    wGoctadXGforestS7c17nGT20Nums, 2048), (wGoctadXGforestS7c17nGT21Labs,
    wGoctadXGforestS7c17nGT21Nums, 2048), (wGoctadXGforestS7c17nGT22Labs,
    wGoctadXGforestS7c17nGT22Nums, 1026)] 521728 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGoctadXGforestS7c17n_hn : wGoctadXGforestS7c17nL.sden * (octSumZ 64 false
    wGoctadXGforestS7c17nL wGoctadXGforestS7c17nW : ℚ) / 8 =
    wGoctadXGforestS7c17nW.sden * (selfOctP wGoctadXGforestS7c17nW : ℚ) := by
  rw [wGoctadXGforestS7c17n_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64
      wGoctadXGforestS7c17nW _ 521728 wGoctadXGforestS7c17n_Wsh wGoctadXGforestS7c17n_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
