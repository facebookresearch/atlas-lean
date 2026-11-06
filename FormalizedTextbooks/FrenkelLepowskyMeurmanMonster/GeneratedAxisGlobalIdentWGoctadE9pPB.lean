/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE9pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh

/-! # Factory parts (octads) of the identification Eighth[13]+ <-> Seventh[14]+ (record
goctad:E9+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGoctadE9p_chk : OctadDense.octSumChk 64 5 true [(wGoctadE9pHT0Labs, wGoctadE9pHT0Nums,
    2048), (wGoctadE9pHT1Labs, wGoctadE9pHT1Nums, 2048), (wGoctadE9pHT2Labs, wGoctadE9pHT2Nums,
    2048), (wGoctadE9pHT3Labs, wGoctadE9pHT3Nums, 2048), (wGoctadE9pHT4Labs, wGoctadE9pHT4Nums,
    2048), (wGoctadE9pHT5Labs, wGoctadE9pHT5Nums, 2048), (wGoctadE9pHT6Labs, wGoctadE9pHT6Nums,
    2048), (wGoctadE9pHT7Labs, wGoctadE9pHT7Nums, 2048), (wGoctadE9pHT8Labs, wGoctadE9pHT8Nums,
    2048), (wGoctadE9pHT9Labs, wGoctadE9pHT9Nums, 2048), (wGoctadE9pHT10Labs, wGoctadE9pHT10Nums,
    2048), (wGoctadE9pHT11Labs, wGoctadE9pHT11Nums, 2048), (wGoctadE9pHT12Labs,
    wGoctadE9pHT12Nums, 2048), (wGoctadE9pHT13Labs, wGoctadE9pHT13Nums, 2048),
    (wGoctadE9pHT14Labs, wGoctadE9pHT14Nums, 2048), (wGoctadE9pHT15Labs, wGoctadE9pHT15Nums,
    2048), (wGoctadE9pHT16Labs, wGoctadE9pHT16Nums, 2048), (wGoctadE9pHT17Labs,
    wGoctadE9pHT17Nums, 2048), (wGoctadE9pHT18Labs, wGoctadE9pHT18Nums, 2048),
    (wGoctadE9pHT19Labs, wGoctadE9pHT19Nums, 2048), (wGoctadE9pHT20Labs, wGoctadE9pHT20Nums,
    2048), (wGoctadE9pHT21Labs, wGoctadE9pHT21Nums, 668)] [(wGoctadE9pGT0Labs, wGoctadE9pGT0Nums,
    2048), (wGoctadE9pGT1Labs, wGoctadE9pGT1Nums, 2048), (wGoctadE9pGT2Labs, wGoctadE9pGT2Nums,
    2048), (wGoctadE9pGT3Labs, wGoctadE9pGT3Nums, 2048), (wGoctadE9pGT4Labs, wGoctadE9pGT4Nums,
    2048), (wGoctadE9pGT5Labs, wGoctadE9pGT5Nums, 2048), (wGoctadE9pGT6Labs, wGoctadE9pGT6Nums,
    2048), (wGoctadE9pGT7Labs, wGoctadE9pGT7Nums, 2048), (wGoctadE9pGT8Labs, wGoctadE9pGT8Nums,
    2048), (wGoctadE9pGT9Labs, wGoctadE9pGT9Nums, 2048), (wGoctadE9pGT10Labs, wGoctadE9pGT10Nums,
    2048), (wGoctadE9pGT11Labs, wGoctadE9pGT11Nums, 2048), (wGoctadE9pGT12Labs,
    wGoctadE9pGT12Nums, 2048), (wGoctadE9pGT13Labs, wGoctadE9pGT13Nums, 1000)] 263392 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGoctadE9p_Lsh : wGoctadE9pL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGoctadE9pHT0Labs, wGoctadE9pHT0Nums, 2048), (wGoctadE9pHT1Labs, wGoctadE9pHT1Nums, 2048),
    (wGoctadE9pHT2Labs, wGoctadE9pHT2Nums, 2048), (wGoctadE9pHT3Labs, wGoctadE9pHT3Nums, 2048),
    (wGoctadE9pHT4Labs, wGoctadE9pHT4Nums, 2048), (wGoctadE9pHT5Labs, wGoctadE9pHT5Nums, 2048),
    (wGoctadE9pHT6Labs, wGoctadE9pHT6Nums, 2048), (wGoctadE9pHT7Labs, wGoctadE9pHT7Nums, 2048),
    (wGoctadE9pHT8Labs, wGoctadE9pHT8Nums, 2048), (wGoctadE9pHT9Labs, wGoctadE9pHT9Nums, 2048),
    (wGoctadE9pHT10Labs, wGoctadE9pHT10Nums, 2048), (wGoctadE9pHT11Labs, wGoctadE9pHT11Nums,
    2048), (wGoctadE9pHT12Labs, wGoctadE9pHT12Nums, 2048), (wGoctadE9pHT13Labs,
    wGoctadE9pHT13Nums, 2048), (wGoctadE9pHT14Labs, wGoctadE9pHT14Nums, 2048),
    (wGoctadE9pHT15Labs, wGoctadE9pHT15Nums, 2048), (wGoctadE9pHT16Labs, wGoctadE9pHT16Nums,
    2048), (wGoctadE9pHT17Labs, wGoctadE9pHT17Nums, 2048), (wGoctadE9pHT18Labs,
    wGoctadE9pHT18Nums, 2048), (wGoctadE9pHT19Labs, wGoctadE9pHT19Nums, 2048),
    (wGoctadE9pHT20Labs, wGoctadE9pHT20Nums, 2048), (wGoctadE9pHT21Labs, wGoctadE9pHT21Nums,
    668)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGoctadE9p_Wsh : wGoctadE9pW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGoctadE9pGT0Labs, wGoctadE9pGT0Nums, 2048), (wGoctadE9pGT1Labs, wGoctadE9pGT1Nums, 2048),
    (wGoctadE9pGT2Labs, wGoctadE9pGT2Nums, 2048), (wGoctadE9pGT3Labs, wGoctadE9pGT3Nums, 2048),
    (wGoctadE9pGT4Labs, wGoctadE9pGT4Nums, 2048), (wGoctadE9pGT5Labs, wGoctadE9pGT5Nums, 2048),
    (wGoctadE9pGT6Labs, wGoctadE9pGT6Nums, 2048), (wGoctadE9pGT7Labs, wGoctadE9pGT7Nums, 2048),
    (wGoctadE9pGT8Labs, wGoctadE9pGT8Nums, 2048), (wGoctadE9pGT9Labs, wGoctadE9pGT9Nums, 2048),
    (wGoctadE9pGT10Labs, wGoctadE9pGT10Nums, 2048), (wGoctadE9pGT11Labs, wGoctadE9pGT11Nums,
    2048), (wGoctadE9pGT12Labs, wGoctadE9pGT12Nums, 2048), (wGoctadE9pGT13Labs,
    wGoctadE9pGT13Nums, 1000)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGoctadE9p_hok : octPackOk 64 wGoctadE9pL = true :=
  OctadDense.octPackOk_of_chk 64 5 true wGoctadE9pL _ _ 263392 wGoctadE9p_Lsh wGoctadE9p_chk

/-- The octad integer sum. -/
theorem wGoctadE9p_octn : octSumZ 64 true wGoctadE9pL wGoctadE9pW = 263392 :=
  OctadDense.octSumZ_of_chk 64 5 true wGoctadE9pL wGoctadE9pW _ _ 263392 wGoctadE9p_Lsh
      wGoctadE9p_Wsh wGoctadE9p_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGoctadE9p_selfchk : OctadDense.selfOctChk 64 [(wGoctadE9pGT0Labs, wGoctadE9pGT0Nums,
    2048), (wGoctadE9pGT1Labs, wGoctadE9pGT1Nums, 2048), (wGoctadE9pGT2Labs, wGoctadE9pGT2Nums,
    2048), (wGoctadE9pGT3Labs, wGoctadE9pGT3Nums, 2048), (wGoctadE9pGT4Labs, wGoctadE9pGT4Nums,
    2048), (wGoctadE9pGT5Labs, wGoctadE9pGT5Nums, 2048), (wGoctadE9pGT6Labs, wGoctadE9pGT6Nums,
    2048), (wGoctadE9pGT7Labs, wGoctadE9pGT7Nums, 2048), (wGoctadE9pGT8Labs, wGoctadE9pGT8Nums,
    2048), (wGoctadE9pGT9Labs, wGoctadE9pGT9Nums, 2048), (wGoctadE9pGT10Labs, wGoctadE9pGT10Nums,
    2048), (wGoctadE9pGT11Labs, wGoctadE9pGT11Nums, 2048), (wGoctadE9pGT12Labs,
    wGoctadE9pGT12Nums, 2048), (wGoctadE9pGT13Labs, wGoctadE9pGT13Nums, 1000)] 32924 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGoctadE9p_hn : wGoctadE9pL.sden * (octSumZ 64 true wGoctadE9pL wGoctadE9pW : ℚ) / 8 =
    wGoctadE9pW.sden * (selfOctP wGoctadE9pW : ℚ) := by
  rw [wGoctadE9p_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGoctadE9pW _ 32924
      wGoctadE9p_Wsh wGoctadE9p_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
