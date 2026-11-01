/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE26nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh

/-! # Factory parts (octads) of the identification Eighth[37]- <-> Seventh[1]+ (record
goctad:E26-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGoctadE26n_chk : OctadDense.octSumChk 64 5 false [(wGoctadE26nHT0Labs,
    wGoctadE26nHT0Nums, 2048), (wGoctadE26nHT1Labs, wGoctadE26nHT1Nums, 2048),
    (wGoctadE26nHT2Labs, wGoctadE26nHT2Nums, 2048), (wGoctadE26nHT3Labs, wGoctadE26nHT3Nums,
    2048), (wGoctadE26nHT4Labs, wGoctadE26nHT4Nums, 2048), (wGoctadE26nHT5Labs,
    wGoctadE26nHT5Nums, 2048), (wGoctadE26nHT6Labs, wGoctadE26nHT6Nums, 2048),
    (wGoctadE26nHT7Labs, wGoctadE26nHT7Nums, 2048), (wGoctadE26nHT8Labs, wGoctadE26nHT8Nums,
    2048), (wGoctadE26nHT9Labs, wGoctadE26nHT9Nums, 2048), (wGoctadE26nHT10Labs,
    wGoctadE26nHT10Nums, 2048), (wGoctadE26nHT11Labs, wGoctadE26nHT11Nums, 2048),
    (wGoctadE26nHT12Labs, wGoctadE26nHT12Nums, 2048), (wGoctadE26nHT13Labs, wGoctadE26nHT13Nums,
    2048), (wGoctadE26nHT14Labs, wGoctadE26nHT14Nums, 2048), (wGoctadE26nHT15Labs,
    wGoctadE26nHT15Nums, 2048), (wGoctadE26nHT16Labs, wGoctadE26nHT16Nums, 2048),
    (wGoctadE26nHT17Labs, wGoctadE26nHT17Nums, 2048), (wGoctadE26nHT18Labs, wGoctadE26nHT18Nums,
    2048), (wGoctadE26nHT19Labs, wGoctadE26nHT19Nums, 2048), (wGoctadE26nHT20Labs,
    wGoctadE26nHT20Nums, 2048), (wGoctadE26nHT21Labs, wGoctadE26nHT21Nums, 668)]
    [(wGoctadE26nGT0Labs, wGoctadE26nGT0Nums, 2048), (wGoctadE26nGT1Labs, wGoctadE26nGT1Nums,
    2048), (wGoctadE26nGT2Labs, wGoctadE26nGT2Nums, 2048), (wGoctadE26nGT3Labs,
    wGoctadE26nGT3Nums, 2048), (wGoctadE26nGT4Labs, wGoctadE26nGT4Nums, 2048),
    (wGoctadE26nGT5Labs, wGoctadE26nGT5Nums, 2048), (wGoctadE26nGT6Labs, wGoctadE26nGT6Nums,
    2048), (wGoctadE26nGT7Labs, wGoctadE26nGT7Nums, 2048), (wGoctadE26nGT8Labs,
    wGoctadE26nGT8Nums, 2048), (wGoctadE26nGT9Labs, wGoctadE26nGT9Nums, 2048),
    (wGoctadE26nGT10Labs, wGoctadE26nGT10Nums, 2048), (wGoctadE26nGT11Labs, wGoctadE26nGT11Nums,
    2048), (wGoctadE26nGT12Labs, wGoctadE26nGT12Nums, 2048), (wGoctadE26nGT13Labs,
    wGoctadE26nGT13Nums, 1000)] 268032 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGoctadE26n_Lsh : wGoctadE26nL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGoctadE26nHT0Labs, wGoctadE26nHT0Nums, 2048), (wGoctadE26nHT1Labs, wGoctadE26nHT1Nums,
    2048), (wGoctadE26nHT2Labs, wGoctadE26nHT2Nums, 2048), (wGoctadE26nHT3Labs,
    wGoctadE26nHT3Nums, 2048), (wGoctadE26nHT4Labs, wGoctadE26nHT4Nums, 2048),
    (wGoctadE26nHT5Labs, wGoctadE26nHT5Nums, 2048), (wGoctadE26nHT6Labs, wGoctadE26nHT6Nums,
    2048), (wGoctadE26nHT7Labs, wGoctadE26nHT7Nums, 2048), (wGoctadE26nHT8Labs,
    wGoctadE26nHT8Nums, 2048), (wGoctadE26nHT9Labs, wGoctadE26nHT9Nums, 2048),
    (wGoctadE26nHT10Labs, wGoctadE26nHT10Nums, 2048), (wGoctadE26nHT11Labs, wGoctadE26nHT11Nums,
    2048), (wGoctadE26nHT12Labs, wGoctadE26nHT12Nums, 2048), (wGoctadE26nHT13Labs,
    wGoctadE26nHT13Nums, 2048), (wGoctadE26nHT14Labs, wGoctadE26nHT14Nums, 2048),
    (wGoctadE26nHT15Labs, wGoctadE26nHT15Nums, 2048), (wGoctadE26nHT16Labs, wGoctadE26nHT16Nums,
    2048), (wGoctadE26nHT17Labs, wGoctadE26nHT17Nums, 2048), (wGoctadE26nHT18Labs,
    wGoctadE26nHT18Nums, 2048), (wGoctadE26nHT19Labs, wGoctadE26nHT19Nums, 2048),
    (wGoctadE26nHT20Labs, wGoctadE26nHT20Nums, 2048), (wGoctadE26nHT21Labs, wGoctadE26nHT21Nums,
    668)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGoctadE26n_Wsh : wGoctadE26nW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGoctadE26nGT0Labs, wGoctadE26nGT0Nums, 2048), (wGoctadE26nGT1Labs, wGoctadE26nGT1Nums,
    2048), (wGoctadE26nGT2Labs, wGoctadE26nGT2Nums, 2048), (wGoctadE26nGT3Labs,
    wGoctadE26nGT3Nums, 2048), (wGoctadE26nGT4Labs, wGoctadE26nGT4Nums, 2048),
    (wGoctadE26nGT5Labs, wGoctadE26nGT5Nums, 2048), (wGoctadE26nGT6Labs, wGoctadE26nGT6Nums,
    2048), (wGoctadE26nGT7Labs, wGoctadE26nGT7Nums, 2048), (wGoctadE26nGT8Labs,
    wGoctadE26nGT8Nums, 2048), (wGoctadE26nGT9Labs, wGoctadE26nGT9Nums, 2048),
    (wGoctadE26nGT10Labs, wGoctadE26nGT10Nums, 2048), (wGoctadE26nGT11Labs, wGoctadE26nGT11Nums,
    2048), (wGoctadE26nGT12Labs, wGoctadE26nGT12Nums, 2048), (wGoctadE26nGT13Labs,
    wGoctadE26nGT13Nums, 1000)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGoctadE26n_hok : octPackOk 64 wGoctadE26nL = true :=
  OctadDense.octPackOk_of_chk 64 5 false wGoctadE26nL _ _ 268032 wGoctadE26n_Lsh wGoctadE26n_chk

/-- The octad integer sum. -/
theorem wGoctadE26n_octn : octSumZ 64 false wGoctadE26nL wGoctadE26nW = 268032 :=
  OctadDense.octSumZ_of_chk 64 5 false wGoctadE26nL wGoctadE26nW _ _ 268032 wGoctadE26n_Lsh
      wGoctadE26n_Wsh wGoctadE26n_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGoctadE26n_selfchk : OctadDense.selfOctChk 64 [(wGoctadE26nGT0Labs, wGoctadE26nGT0Nums,
    2048), (wGoctadE26nGT1Labs, wGoctadE26nGT1Nums, 2048), (wGoctadE26nGT2Labs,
    wGoctadE26nGT2Nums, 2048), (wGoctadE26nGT3Labs, wGoctadE26nGT3Nums, 2048),
    (wGoctadE26nGT4Labs, wGoctadE26nGT4Nums, 2048), (wGoctadE26nGT5Labs, wGoctadE26nGT5Nums,
    2048), (wGoctadE26nGT6Labs, wGoctadE26nGT6Nums, 2048), (wGoctadE26nGT7Labs,
    wGoctadE26nGT7Nums, 2048), (wGoctadE26nGT8Labs, wGoctadE26nGT8Nums, 2048),
    (wGoctadE26nGT9Labs, wGoctadE26nGT9Nums, 2048), (wGoctadE26nGT10Labs, wGoctadE26nGT10Nums,
    2048), (wGoctadE26nGT11Labs, wGoctadE26nGT11Nums, 2048), (wGoctadE26nGT12Labs,
    wGoctadE26nGT12Nums, 2048), (wGoctadE26nGT13Labs, wGoctadE26nGT13Nums, 1000)] 33504 = true :=
    by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGoctadE26n_hn : wGoctadE26nL.sden * (octSumZ 64 false wGoctadE26nL wGoctadE26nW : ℚ) / 8 =
    wGoctadE26nW.sden * (selfOctP wGoctadE26nW : ℚ) := by
  rw [wGoctadE26n_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGoctadE26nW _ 33504
      wGoctadE26n_Wsh wGoctadE26n_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
