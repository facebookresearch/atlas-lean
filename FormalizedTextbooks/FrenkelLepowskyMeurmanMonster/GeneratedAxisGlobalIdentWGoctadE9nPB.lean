/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE9nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT

/-! # Factory parts (octads) of the identification Eighth[13]- <-> Eighth[13]- (record goctad:E9-,
e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGoctadE9n_chk : OctadDense.octSumChk 64 5 false [(wGoctadE9nHT0Labs, wGoctadE9nHT0Nums,
    2048), (wGoctadE9nHT1Labs, wGoctadE9nHT1Nums, 2048), (wGoctadE9nHT2Labs, wGoctadE9nHT2Nums,
    2048), (wGoctadE9nHT3Labs, wGoctadE9nHT3Nums, 2048), (wGoctadE9nHT4Labs, wGoctadE9nHT4Nums,
    2048), (wGoctadE9nHT5Labs, wGoctadE9nHT5Nums, 2048), (wGoctadE9nHT6Labs, wGoctadE9nHT6Nums,
    2048), (wGoctadE9nHT7Labs, wGoctadE9nHT7Nums, 2048), (wGoctadE9nHT8Labs, wGoctadE9nHT8Nums,
    2048), (wGoctadE9nHT9Labs, wGoctadE9nHT9Nums, 2048), (wGoctadE9nHT10Labs, wGoctadE9nHT10Nums,
    2048), (wGoctadE9nHT11Labs, wGoctadE9nHT11Nums, 2048), (wGoctadE9nHT12Labs,
    wGoctadE9nHT12Nums, 2048), (wGoctadE9nHT13Labs, wGoctadE9nHT13Nums, 2048),
    (wGoctadE9nHT14Labs, wGoctadE9nHT14Nums, 2048), (wGoctadE9nHT15Labs, wGoctadE9nHT15Nums,
    2048), (wGoctadE9nHT16Labs, wGoctadE9nHT16Nums, 2048), (wGoctadE9nHT17Labs,
    wGoctadE9nHT17Nums, 2048), (wGoctadE9nHT18Labs, wGoctadE9nHT18Nums, 2048),
    (wGoctadE9nHT19Labs, wGoctadE9nHT19Nums, 2048), (wGoctadE9nHT20Labs, wGoctadE9nHT20Nums,
    2048), (wGoctadE9nHT21Labs, wGoctadE9nHT21Nums, 668)] [(wGoctadE9nGT0Labs, wGoctadE9nGT0Nums,
    2048), (wGoctadE9nGT1Labs, wGoctadE9nGT1Nums, 2048), (wGoctadE9nGT2Labs, wGoctadE9nGT2Nums,
    2048), (wGoctadE9nGT3Labs, wGoctadE9nGT3Nums, 2048), (wGoctadE9nGT4Labs, wGoctadE9nGT4Nums,
    2048), (wGoctadE9nGT5Labs, wGoctadE9nGT5Nums, 2048), (wGoctadE9nGT6Labs, wGoctadE9nGT6Nums,
    2048), (wGoctadE9nGT7Labs, wGoctadE9nGT7Nums, 2048), (wGoctadE9nGT8Labs, wGoctadE9nGT8Nums,
    2048), (wGoctadE9nGT9Labs, wGoctadE9nGT9Nums, 2048), (wGoctadE9nGT10Labs, wGoctadE9nGT10Nums,
    2048), (wGoctadE9nGT11Labs, wGoctadE9nGT11Nums, 2048), (wGoctadE9nGT12Labs,
    wGoctadE9nGT12Nums, 2048), (wGoctadE9nGT13Labs, wGoctadE9nGT13Nums, 2048),
    (wGoctadE9nGT14Labs, wGoctadE9nGT14Nums, 2048), (wGoctadE9nGT15Labs, wGoctadE9nGT15Nums,
    2048), (wGoctadE9nGT16Labs, wGoctadE9nGT16Nums, 2048), (wGoctadE9nGT17Labs,
    wGoctadE9nGT17Nums, 2048), (wGoctadE9nGT18Labs, wGoctadE9nGT18Nums, 2048),
    (wGoctadE9nGT19Labs, wGoctadE9nGT19Nums, 2048), (wGoctadE9nGT20Labs, wGoctadE9nGT20Nums,
    2048), (wGoctadE9nGT21Labs, wGoctadE9nGT21Nums, 668)] 263392 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGoctadE9n_Lsh : wGoctadE9nL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGoctadE9nHT0Labs, wGoctadE9nHT0Nums, 2048), (wGoctadE9nHT1Labs, wGoctadE9nHT1Nums, 2048),
    (wGoctadE9nHT2Labs, wGoctadE9nHT2Nums, 2048), (wGoctadE9nHT3Labs, wGoctadE9nHT3Nums, 2048),
    (wGoctadE9nHT4Labs, wGoctadE9nHT4Nums, 2048), (wGoctadE9nHT5Labs, wGoctadE9nHT5Nums, 2048),
    (wGoctadE9nHT6Labs, wGoctadE9nHT6Nums, 2048), (wGoctadE9nHT7Labs, wGoctadE9nHT7Nums, 2048),
    (wGoctadE9nHT8Labs, wGoctadE9nHT8Nums, 2048), (wGoctadE9nHT9Labs, wGoctadE9nHT9Nums, 2048),
    (wGoctadE9nHT10Labs, wGoctadE9nHT10Nums, 2048), (wGoctadE9nHT11Labs, wGoctadE9nHT11Nums,
    2048), (wGoctadE9nHT12Labs, wGoctadE9nHT12Nums, 2048), (wGoctadE9nHT13Labs,
    wGoctadE9nHT13Nums, 2048), (wGoctadE9nHT14Labs, wGoctadE9nHT14Nums, 2048),
    (wGoctadE9nHT15Labs, wGoctadE9nHT15Nums, 2048), (wGoctadE9nHT16Labs, wGoctadE9nHT16Nums,
    2048), (wGoctadE9nHT17Labs, wGoctadE9nHT17Nums, 2048), (wGoctadE9nHT18Labs,
    wGoctadE9nHT18Nums, 2048), (wGoctadE9nHT19Labs, wGoctadE9nHT19Nums, 2048),
    (wGoctadE9nHT20Labs, wGoctadE9nHT20Nums, 2048), (wGoctadE9nHT21Labs, wGoctadE9nHT21Nums,
    668)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGoctadE9n_Wsh : wGoctadE9nW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGoctadE9nGT0Labs, wGoctadE9nGT0Nums, 2048), (wGoctadE9nGT1Labs, wGoctadE9nGT1Nums, 2048),
    (wGoctadE9nGT2Labs, wGoctadE9nGT2Nums, 2048), (wGoctadE9nGT3Labs, wGoctadE9nGT3Nums, 2048),
    (wGoctadE9nGT4Labs, wGoctadE9nGT4Nums, 2048), (wGoctadE9nGT5Labs, wGoctadE9nGT5Nums, 2048),
    (wGoctadE9nGT6Labs, wGoctadE9nGT6Nums, 2048), (wGoctadE9nGT7Labs, wGoctadE9nGT7Nums, 2048),
    (wGoctadE9nGT8Labs, wGoctadE9nGT8Nums, 2048), (wGoctadE9nGT9Labs, wGoctadE9nGT9Nums, 2048),
    (wGoctadE9nGT10Labs, wGoctadE9nGT10Nums, 2048), (wGoctadE9nGT11Labs, wGoctadE9nGT11Nums,
    2048), (wGoctadE9nGT12Labs, wGoctadE9nGT12Nums, 2048), (wGoctadE9nGT13Labs,
    wGoctadE9nGT13Nums, 2048), (wGoctadE9nGT14Labs, wGoctadE9nGT14Nums, 2048),
    (wGoctadE9nGT15Labs, wGoctadE9nGT15Nums, 2048), (wGoctadE9nGT16Labs, wGoctadE9nGT16Nums,
    2048), (wGoctadE9nGT17Labs, wGoctadE9nGT17Nums, 2048), (wGoctadE9nGT18Labs,
    wGoctadE9nGT18Nums, 2048), (wGoctadE9nGT19Labs, wGoctadE9nGT19Nums, 2048),
    (wGoctadE9nGT20Labs, wGoctadE9nGT20Nums, 2048), (wGoctadE9nGT21Labs, wGoctadE9nGT21Nums,
    668)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGoctadE9n_hok : octPackOk 64 wGoctadE9nL = true :=
  OctadDense.octPackOk_of_chk 64 5 false wGoctadE9nL _ _ 263392 wGoctadE9n_Lsh wGoctadE9n_chk

/-- The octad integer sum. -/
theorem wGoctadE9n_octn : octSumZ 64 false wGoctadE9nL wGoctadE9nW = 263392 :=
  OctadDense.octSumZ_of_chk 64 5 false wGoctadE9nL wGoctadE9nW _ _ 263392 wGoctadE9n_Lsh
      wGoctadE9n_Wsh wGoctadE9n_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGoctadE9n_selfchk : OctadDense.selfOctChk 64 [(wGoctadE9nGT0Labs, wGoctadE9nGT0Nums,
    2048), (wGoctadE9nGT1Labs, wGoctadE9nGT1Nums, 2048), (wGoctadE9nGT2Labs, wGoctadE9nGT2Nums,
    2048), (wGoctadE9nGT3Labs, wGoctadE9nGT3Nums, 2048), (wGoctadE9nGT4Labs, wGoctadE9nGT4Nums,
    2048), (wGoctadE9nGT5Labs, wGoctadE9nGT5Nums, 2048), (wGoctadE9nGT6Labs, wGoctadE9nGT6Nums,
    2048), (wGoctadE9nGT7Labs, wGoctadE9nGT7Nums, 2048), (wGoctadE9nGT8Labs, wGoctadE9nGT8Nums,
    2048), (wGoctadE9nGT9Labs, wGoctadE9nGT9Nums, 2048), (wGoctadE9nGT10Labs, wGoctadE9nGT10Nums,
    2048), (wGoctadE9nGT11Labs, wGoctadE9nGT11Nums, 2048), (wGoctadE9nGT12Labs,
    wGoctadE9nGT12Nums, 2048), (wGoctadE9nGT13Labs, wGoctadE9nGT13Nums, 2048),
    (wGoctadE9nGT14Labs, wGoctadE9nGT14Nums, 2048), (wGoctadE9nGT15Labs, wGoctadE9nGT15Nums,
    2048), (wGoctadE9nGT16Labs, wGoctadE9nGT16Nums, 2048), (wGoctadE9nGT17Labs,
    wGoctadE9nGT17Nums, 2048), (wGoctadE9nGT18Labs, wGoctadE9nGT18Nums, 2048),
    (wGoctadE9nGT19Labs, wGoctadE9nGT19Nums, 2048), (wGoctadE9nGT20Labs, wGoctadE9nGT20Nums,
    2048), (wGoctadE9nGT21Labs, wGoctadE9nGT21Nums, 668)] 32924 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGoctadE9n_hn : wGoctadE9nL.sden * (octSumZ 64 false wGoctadE9nL wGoctadE9nW : ℚ) / 8 =
    wGoctadE9nW.sden * (selfOctP wGoctadE9nW : ℚ) := by
  rw [wGoctadE9n_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGoctadE9nW _ 32924
      wGoctadE9n_Wsh wGoctadE9n_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
