/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c14pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT

/-! # Factory parts (octads) of the identification Eighth[27]+ <-> Seventh[22]+ (record
gforest:S7c14+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGforestS7c14p_chk : OctadDense.octSumChk 64 5 true [(wGforestS7c14pHT0Labs,
    wGforestS7c14pHT0Nums, 2048), (wGforestS7c14pHT1Labs, wGforestS7c14pHT1Nums, 2048),
    (wGforestS7c14pHT2Labs, wGforestS7c14pHT2Nums, 2048), (wGforestS7c14pHT3Labs,
    wGforestS7c14pHT3Nums, 2048), (wGforestS7c14pHT4Labs, wGforestS7c14pHT4Nums, 2048),
    (wGforestS7c14pHT5Labs, wGforestS7c14pHT5Nums, 2048), (wGforestS7c14pHT6Labs,
    wGforestS7c14pHT6Nums, 2048), (wGforestS7c14pHT7Labs, wGforestS7c14pHT7Nums, 2048),
    (wGforestS7c14pHT8Labs, wGforestS7c14pHT8Nums, 2048), (wGforestS7c14pHT9Labs,
    wGforestS7c14pHT9Nums, 2048), (wGforestS7c14pHT10Labs, wGforestS7c14pHT10Nums, 2048),
    (wGforestS7c14pHT11Labs, wGforestS7c14pHT11Nums, 2048), (wGforestS7c14pHT12Labs,
    wGforestS7c14pHT12Nums, 2048), (wGforestS7c14pHT13Labs, wGforestS7c14pHT13Nums, 1000)]
    [(wGforestS7c14pGT0Labs, wGforestS7c14pGT0Nums, 2048), (wGforestS7c14pGT1Labs,
    wGforestS7c14pGT1Nums, 2048), (wGforestS7c14pGT2Labs, wGforestS7c14pGT2Nums, 2048),
    (wGforestS7c14pGT3Labs, wGforestS7c14pGT3Nums, 2048), (wGforestS7c14pGT4Labs,
    wGforestS7c14pGT4Nums, 2048), (wGforestS7c14pGT5Labs, wGforestS7c14pGT5Nums, 2048),
    (wGforestS7c14pGT6Labs, wGforestS7c14pGT6Nums, 2048), (wGforestS7c14pGT7Labs,
    wGforestS7c14pGT7Nums, 2048), (wGforestS7c14pGT8Labs, wGforestS7c14pGT8Nums, 2048),
    (wGforestS7c14pGT9Labs, wGforestS7c14pGT9Nums, 2048), (wGforestS7c14pGT10Labs,
    wGforestS7c14pGT10Nums, 2048), (wGforestS7c14pGT11Labs, wGforestS7c14pGT11Nums, 2048),
    (wGforestS7c14pGT12Labs, wGforestS7c14pGT12Nums, 2048), (wGforestS7c14pGT13Labs,
    wGforestS7c14pGT13Nums, 2048), (wGforestS7c14pGT14Labs, wGforestS7c14pGT14Nums, 2048),
    (wGforestS7c14pGT15Labs, wGforestS7c14pGT15Nums, 2048), (wGforestS7c14pGT16Labs,
    wGforestS7c14pGT16Nums, 2048), (wGforestS7c14pGT17Labs, wGforestS7c14pGT17Nums, 2048),
    (wGforestS7c14pGT18Labs, wGforestS7c14pGT18Nums, 2048), (wGforestS7c14pGT19Labs,
    wGforestS7c14pGT19Nums, 2048), (wGforestS7c14pGT20Labs, wGforestS7c14pGT20Nums, 2048),
    (wGforestS7c14pGT21Labs, wGforestS7c14pGT21Nums, 668)] 263392 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGforestS7c14p_Lsh : wGforestS7c14pL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGforestS7c14pHT0Labs, wGforestS7c14pHT0Nums, 2048), (wGforestS7c14pHT1Labs,
    wGforestS7c14pHT1Nums, 2048), (wGforestS7c14pHT2Labs, wGforestS7c14pHT2Nums, 2048),
    (wGforestS7c14pHT3Labs, wGforestS7c14pHT3Nums, 2048), (wGforestS7c14pHT4Labs,
    wGforestS7c14pHT4Nums, 2048), (wGforestS7c14pHT5Labs, wGforestS7c14pHT5Nums, 2048),
    (wGforestS7c14pHT6Labs, wGforestS7c14pHT6Nums, 2048), (wGforestS7c14pHT7Labs,
    wGforestS7c14pHT7Nums, 2048), (wGforestS7c14pHT8Labs, wGforestS7c14pHT8Nums, 2048),
    (wGforestS7c14pHT9Labs, wGforestS7c14pHT9Nums, 2048), (wGforestS7c14pHT10Labs,
    wGforestS7c14pHT10Nums, 2048), (wGforestS7c14pHT11Labs, wGforestS7c14pHT11Nums, 2048),
    (wGforestS7c14pHT12Labs, wGforestS7c14pHT12Nums, 2048), (wGforestS7c14pHT13Labs,
    wGforestS7c14pHT13Nums, 1000)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGforestS7c14p_Wsh : wGforestS7c14pW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGforestS7c14pGT0Labs, wGforestS7c14pGT0Nums, 2048), (wGforestS7c14pGT1Labs,
    wGforestS7c14pGT1Nums, 2048), (wGforestS7c14pGT2Labs, wGforestS7c14pGT2Nums, 2048),
    (wGforestS7c14pGT3Labs, wGforestS7c14pGT3Nums, 2048), (wGforestS7c14pGT4Labs,
    wGforestS7c14pGT4Nums, 2048), (wGforestS7c14pGT5Labs, wGforestS7c14pGT5Nums, 2048),
    (wGforestS7c14pGT6Labs, wGforestS7c14pGT6Nums, 2048), (wGforestS7c14pGT7Labs,
    wGforestS7c14pGT7Nums, 2048), (wGforestS7c14pGT8Labs, wGforestS7c14pGT8Nums, 2048),
    (wGforestS7c14pGT9Labs, wGforestS7c14pGT9Nums, 2048), (wGforestS7c14pGT10Labs,
    wGforestS7c14pGT10Nums, 2048), (wGforestS7c14pGT11Labs, wGforestS7c14pGT11Nums, 2048),
    (wGforestS7c14pGT12Labs, wGforestS7c14pGT12Nums, 2048), (wGforestS7c14pGT13Labs,
    wGforestS7c14pGT13Nums, 2048), (wGforestS7c14pGT14Labs, wGforestS7c14pGT14Nums, 2048),
    (wGforestS7c14pGT15Labs, wGforestS7c14pGT15Nums, 2048), (wGforestS7c14pGT16Labs,
    wGforestS7c14pGT16Nums, 2048), (wGforestS7c14pGT17Labs, wGforestS7c14pGT17Nums, 2048),
    (wGforestS7c14pGT18Labs, wGforestS7c14pGT18Nums, 2048), (wGforestS7c14pGT19Labs,
    wGforestS7c14pGT19Nums, 2048), (wGforestS7c14pGT20Labs, wGforestS7c14pGT20Nums, 2048),
    (wGforestS7c14pGT21Labs, wGforestS7c14pGT21Nums, 668)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGforestS7c14p_hok : octPackOk 64 wGforestS7c14pL = true :=
  OctadDense.octPackOk_of_chk 64 5 true wGforestS7c14pL _ _ 263392 wGforestS7c14p_Lsh
      wGforestS7c14p_chk

/-- The octad integer sum. -/
theorem wGforestS7c14p_octn : octSumZ 64 true wGforestS7c14pL wGforestS7c14pW = 263392 :=
  OctadDense.octSumZ_of_chk 64 5 true wGforestS7c14pL wGforestS7c14pW _ _ 263392
      wGforestS7c14p_Lsh wGforestS7c14p_Wsh wGforestS7c14p_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGforestS7c14p_selfchk : OctadDense.selfOctChk 64 [(wGforestS7c14pGT0Labs,
    wGforestS7c14pGT0Nums, 2048), (wGforestS7c14pGT1Labs, wGforestS7c14pGT1Nums, 2048),
    (wGforestS7c14pGT2Labs, wGforestS7c14pGT2Nums, 2048), (wGforestS7c14pGT3Labs,
    wGforestS7c14pGT3Nums, 2048), (wGforestS7c14pGT4Labs, wGforestS7c14pGT4Nums, 2048),
    (wGforestS7c14pGT5Labs, wGforestS7c14pGT5Nums, 2048), (wGforestS7c14pGT6Labs,
    wGforestS7c14pGT6Nums, 2048), (wGforestS7c14pGT7Labs, wGforestS7c14pGT7Nums, 2048),
    (wGforestS7c14pGT8Labs, wGforestS7c14pGT8Nums, 2048), (wGforestS7c14pGT9Labs,
    wGforestS7c14pGT9Nums, 2048), (wGforestS7c14pGT10Labs, wGforestS7c14pGT10Nums, 2048),
    (wGforestS7c14pGT11Labs, wGforestS7c14pGT11Nums, 2048), (wGforestS7c14pGT12Labs,
    wGforestS7c14pGT12Nums, 2048), (wGforestS7c14pGT13Labs, wGforestS7c14pGT13Nums, 2048),
    (wGforestS7c14pGT14Labs, wGforestS7c14pGT14Nums, 2048), (wGforestS7c14pGT15Labs,
    wGforestS7c14pGT15Nums, 2048), (wGforestS7c14pGT16Labs, wGforestS7c14pGT16Nums, 2048),
    (wGforestS7c14pGT17Labs, wGforestS7c14pGT17Nums, 2048), (wGforestS7c14pGT18Labs,
    wGforestS7c14pGT18Nums, 2048), (wGforestS7c14pGT19Labs, wGforestS7c14pGT19Nums, 2048),
    (wGforestS7c14pGT20Labs, wGforestS7c14pGT20Nums, 2048), (wGforestS7c14pGT21Labs,
    wGforestS7c14pGT21Nums, 668)] 32924 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGforestS7c14p_hn : wGforestS7c14pL.sden * (octSumZ 64 true wGforestS7c14pL
    wGforestS7c14pW : ℚ) / 8 =
    wGforestS7c14pW.sden * (selfOctP wGforestS7c14pW : ℚ) := by
  rw [wGforestS7c14p_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGforestS7c14pW _ 32924
      wGforestS7c14p_Wsh wGforestS7c14p_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
