/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE26pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh

/-! # Factory parts (octads) of the identification Eighth[37]+ <-> Seventh[32]+ (record
goctad:E26+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGoctadE26p_chk : OctadDense.octSumChk 64 5 true [(wGoctadE26pHT0Labs, wGoctadE26pHT0Nums,
    2048), (wGoctadE26pHT1Labs, wGoctadE26pHT1Nums, 2048), (wGoctadE26pHT2Labs,
    wGoctadE26pHT2Nums, 2048), (wGoctadE26pHT3Labs, wGoctadE26pHT3Nums, 2048),
    (wGoctadE26pHT4Labs, wGoctadE26pHT4Nums, 2048), (wGoctadE26pHT5Labs, wGoctadE26pHT5Nums,
    2048), (wGoctadE26pHT6Labs, wGoctadE26pHT6Nums, 2048), (wGoctadE26pHT7Labs,
    wGoctadE26pHT7Nums, 2048), (wGoctadE26pHT8Labs, wGoctadE26pHT8Nums, 2048),
    (wGoctadE26pHT9Labs, wGoctadE26pHT9Nums, 2048), (wGoctadE26pHT10Labs, wGoctadE26pHT10Nums,
    2048), (wGoctadE26pHT11Labs, wGoctadE26pHT11Nums, 2048), (wGoctadE26pHT12Labs,
    wGoctadE26pHT12Nums, 2048), (wGoctadE26pHT13Labs, wGoctadE26pHT13Nums, 2048),
    (wGoctadE26pHT14Labs, wGoctadE26pHT14Nums, 2048), (wGoctadE26pHT15Labs, wGoctadE26pHT15Nums,
    2048), (wGoctadE26pHT16Labs, wGoctadE26pHT16Nums, 2048), (wGoctadE26pHT17Labs,
    wGoctadE26pHT17Nums, 2048), (wGoctadE26pHT18Labs, wGoctadE26pHT18Nums, 2048),
    (wGoctadE26pHT19Labs, wGoctadE26pHT19Nums, 2048), (wGoctadE26pHT20Labs, wGoctadE26pHT20Nums,
    2048), (wGoctadE26pHT21Labs, wGoctadE26pHT21Nums, 668)] [(wGoctadE26pGT0Labs,
    wGoctadE26pGT0Nums, 2048), (wGoctadE26pGT1Labs, wGoctadE26pGT1Nums, 2048),
    (wGoctadE26pGT2Labs, wGoctadE26pGT2Nums, 2048), (wGoctadE26pGT3Labs, wGoctadE26pGT3Nums,
    2048), (wGoctadE26pGT4Labs, wGoctadE26pGT4Nums, 2048), (wGoctadE26pGT5Labs,
    wGoctadE26pGT5Nums, 2048), (wGoctadE26pGT6Labs, wGoctadE26pGT6Nums, 2048),
    (wGoctadE26pGT7Labs, wGoctadE26pGT7Nums, 2048), (wGoctadE26pGT8Labs, wGoctadE26pGT8Nums,
    2048), (wGoctadE26pGT9Labs, wGoctadE26pGT9Nums, 2048), (wGoctadE26pGT10Labs,
    wGoctadE26pGT10Nums, 2048), (wGoctadE26pGT11Labs, wGoctadE26pGT11Nums, 2048),
    (wGoctadE26pGT12Labs, wGoctadE26pGT12Nums, 2048), (wGoctadE26pGT13Labs, wGoctadE26pGT13Nums,
    1000)] 268032 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGoctadE26p_Lsh : wGoctadE26pL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGoctadE26pHT0Labs, wGoctadE26pHT0Nums, 2048), (wGoctadE26pHT1Labs, wGoctadE26pHT1Nums,
    2048), (wGoctadE26pHT2Labs, wGoctadE26pHT2Nums, 2048), (wGoctadE26pHT3Labs,
    wGoctadE26pHT3Nums, 2048), (wGoctadE26pHT4Labs, wGoctadE26pHT4Nums, 2048),
    (wGoctadE26pHT5Labs, wGoctadE26pHT5Nums, 2048), (wGoctadE26pHT6Labs, wGoctadE26pHT6Nums,
    2048), (wGoctadE26pHT7Labs, wGoctadE26pHT7Nums, 2048), (wGoctadE26pHT8Labs,
    wGoctadE26pHT8Nums, 2048), (wGoctadE26pHT9Labs, wGoctadE26pHT9Nums, 2048),
    (wGoctadE26pHT10Labs, wGoctadE26pHT10Nums, 2048), (wGoctadE26pHT11Labs, wGoctadE26pHT11Nums,
    2048), (wGoctadE26pHT12Labs, wGoctadE26pHT12Nums, 2048), (wGoctadE26pHT13Labs,
    wGoctadE26pHT13Nums, 2048), (wGoctadE26pHT14Labs, wGoctadE26pHT14Nums, 2048),
    (wGoctadE26pHT15Labs, wGoctadE26pHT15Nums, 2048), (wGoctadE26pHT16Labs, wGoctadE26pHT16Nums,
    2048), (wGoctadE26pHT17Labs, wGoctadE26pHT17Nums, 2048), (wGoctadE26pHT18Labs,
    wGoctadE26pHT18Nums, 2048), (wGoctadE26pHT19Labs, wGoctadE26pHT19Nums, 2048),
    (wGoctadE26pHT20Labs, wGoctadE26pHT20Nums, 2048), (wGoctadE26pHT21Labs, wGoctadE26pHT21Nums,
    668)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGoctadE26p_Wsh : wGoctadE26pW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGoctadE26pGT0Labs, wGoctadE26pGT0Nums, 2048), (wGoctadE26pGT1Labs, wGoctadE26pGT1Nums,
    2048), (wGoctadE26pGT2Labs, wGoctadE26pGT2Nums, 2048), (wGoctadE26pGT3Labs,
    wGoctadE26pGT3Nums, 2048), (wGoctadE26pGT4Labs, wGoctadE26pGT4Nums, 2048),
    (wGoctadE26pGT5Labs, wGoctadE26pGT5Nums, 2048), (wGoctadE26pGT6Labs, wGoctadE26pGT6Nums,
    2048), (wGoctadE26pGT7Labs, wGoctadE26pGT7Nums, 2048), (wGoctadE26pGT8Labs,
    wGoctadE26pGT8Nums, 2048), (wGoctadE26pGT9Labs, wGoctadE26pGT9Nums, 2048),
    (wGoctadE26pGT10Labs, wGoctadE26pGT10Nums, 2048), (wGoctadE26pGT11Labs, wGoctadE26pGT11Nums,
    2048), (wGoctadE26pGT12Labs, wGoctadE26pGT12Nums, 2048), (wGoctadE26pGT13Labs,
    wGoctadE26pGT13Nums, 1000)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGoctadE26p_hok : octPackOk 64 wGoctadE26pL = true :=
  OctadDense.octPackOk_of_chk 64 5 true wGoctadE26pL _ _ 268032 wGoctadE26p_Lsh wGoctadE26p_chk

/-- The octad integer sum. -/
theorem wGoctadE26p_octn : octSumZ 64 true wGoctadE26pL wGoctadE26pW = 268032 :=
  OctadDense.octSumZ_of_chk 64 5 true wGoctadE26pL wGoctadE26pW _ _ 268032 wGoctadE26p_Lsh
      wGoctadE26p_Wsh wGoctadE26p_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGoctadE26p_selfchk : OctadDense.selfOctChk 64 [(wGoctadE26pGT0Labs, wGoctadE26pGT0Nums,
    2048), (wGoctadE26pGT1Labs, wGoctadE26pGT1Nums, 2048), (wGoctadE26pGT2Labs,
    wGoctadE26pGT2Nums, 2048), (wGoctadE26pGT3Labs, wGoctadE26pGT3Nums, 2048),
    (wGoctadE26pGT4Labs, wGoctadE26pGT4Nums, 2048), (wGoctadE26pGT5Labs, wGoctadE26pGT5Nums,
    2048), (wGoctadE26pGT6Labs, wGoctadE26pGT6Nums, 2048), (wGoctadE26pGT7Labs,
    wGoctadE26pGT7Nums, 2048), (wGoctadE26pGT8Labs, wGoctadE26pGT8Nums, 2048),
    (wGoctadE26pGT9Labs, wGoctadE26pGT9Nums, 2048), (wGoctadE26pGT10Labs, wGoctadE26pGT10Nums,
    2048), (wGoctadE26pGT11Labs, wGoctadE26pGT11Nums, 2048), (wGoctadE26pGT12Labs,
    wGoctadE26pGT12Nums, 2048), (wGoctadE26pGT13Labs, wGoctadE26pGT13Nums, 1000)] 33504 = true :=
    by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGoctadE26p_hn : wGoctadE26pL.sden * (octSumZ 64 true wGoctadE26pL wGoctadE26pW : ℚ) / 8 =
    wGoctadE26pW.sden * (selfOctP wGoctadE26pW : ℚ) := by
  rw [wGoctadE26p_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGoctadE26pW _ 33504
      wGoctadE26p_Wsh wGoctadE26p_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
