/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c12pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Factory parts (octads) of the identification Root8[10]- <-> Seventh[19]+ (record
gforest:S7c12+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGforestS7c12p_chk : OctadDense.octSumChk 64 6 true [(wGforestS7c12pHT0Labs,
    wGforestS7c12pHT0Nums, 2048), (wGforestS7c12pHT1Labs, wGforestS7c12pHT1Nums, 2048),
    (wGforestS7c12pHT2Labs, wGforestS7c12pHT2Nums, 2048), (wGforestS7c12pHT3Labs,
    wGforestS7c12pHT3Nums, 2048), (wGforestS7c12pHT4Labs, wGforestS7c12pHT4Nums, 2048),
    (wGforestS7c12pHT5Labs, wGforestS7c12pHT5Nums, 2048), (wGforestS7c12pHT6Labs,
    wGforestS7c12pHT6Nums, 2048), (wGforestS7c12pHT7Labs, wGforestS7c12pHT7Nums, 2048),
    (wGforestS7c12pHT8Labs, wGforestS7c12pHT8Nums, 2048), (wGforestS7c12pHT9Labs,
    wGforestS7c12pHT9Nums, 2048), (wGforestS7c12pHT10Labs, wGforestS7c12pHT10Nums, 2048),
    (wGforestS7c12pHT11Labs, wGforestS7c12pHT11Nums, 2048), (wGforestS7c12pHT12Labs,
    wGforestS7c12pHT12Nums, 2048), (wGforestS7c12pHT13Labs, wGforestS7c12pHT13Nums, 1000)]
    [(wGforestS7c12pGT0Labs, wGforestS7c12pGT0Nums, 2048), (wGforestS7c12pGT1Labs,
    wGforestS7c12pGT1Nums, 2048), (wGforestS7c12pGT2Labs, wGforestS7c12pGT2Nums, 2048),
    (wGforestS7c12pGT3Labs, wGforestS7c12pGT3Nums, 2048), (wGforestS7c12pGT4Labs,
    wGforestS7c12pGT4Nums, 2048), (wGforestS7c12pGT5Labs, wGforestS7c12pGT5Nums, 2048),
    (wGforestS7c12pGT6Labs, wGforestS7c12pGT6Nums, 2048), (wGforestS7c12pGT7Labs,
    wGforestS7c12pGT7Nums, 2048), (wGforestS7c12pGT8Labs, wGforestS7c12pGT8Nums, 2048),
    (wGforestS7c12pGT9Labs, wGforestS7c12pGT9Nums, 2048), (wGforestS7c12pGT10Labs,
    wGforestS7c12pGT10Nums, 2048), (wGforestS7c12pGT11Labs, wGforestS7c12pGT11Nums, 2048),
    (wGforestS7c12pGT12Labs, wGforestS7c12pGT12Nums, 2048), (wGforestS7c12pGT13Labs,
    wGforestS7c12pGT13Nums, 2048), (wGforestS7c12pGT14Labs, wGforestS7c12pGT14Nums, 2048),
    (wGforestS7c12pGT15Labs, wGforestS7c12pGT15Nums, 2048), (wGforestS7c12pGT16Labs,
    wGforestS7c12pGT16Nums, 808)] 1031680 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGforestS7c12p_Lsh : wGforestS7c12pL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGforestS7c12pHT0Labs, wGforestS7c12pHT0Nums, 2048), (wGforestS7c12pHT1Labs,
    wGforestS7c12pHT1Nums, 2048), (wGforestS7c12pHT2Labs, wGforestS7c12pHT2Nums, 2048),
    (wGforestS7c12pHT3Labs, wGforestS7c12pHT3Nums, 2048), (wGforestS7c12pHT4Labs,
    wGforestS7c12pHT4Nums, 2048), (wGforestS7c12pHT5Labs, wGforestS7c12pHT5Nums, 2048),
    (wGforestS7c12pHT6Labs, wGforestS7c12pHT6Nums, 2048), (wGforestS7c12pHT7Labs,
    wGforestS7c12pHT7Nums, 2048), (wGforestS7c12pHT8Labs, wGforestS7c12pHT8Nums, 2048),
    (wGforestS7c12pHT9Labs, wGforestS7c12pHT9Nums, 2048), (wGforestS7c12pHT10Labs,
    wGforestS7c12pHT10Nums, 2048), (wGforestS7c12pHT11Labs, wGforestS7c12pHT11Nums, 2048),
    (wGforestS7c12pHT12Labs, wGforestS7c12pHT12Nums, 2048), (wGforestS7c12pHT13Labs,
    wGforestS7c12pHT13Nums, 1000)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGforestS7c12p_Wsh : wGforestS7c12pW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGforestS7c12pGT0Labs, wGforestS7c12pGT0Nums, 2048), (wGforestS7c12pGT1Labs,
    wGforestS7c12pGT1Nums, 2048), (wGforestS7c12pGT2Labs, wGforestS7c12pGT2Nums, 2048),
    (wGforestS7c12pGT3Labs, wGforestS7c12pGT3Nums, 2048), (wGforestS7c12pGT4Labs,
    wGforestS7c12pGT4Nums, 2048), (wGforestS7c12pGT5Labs, wGforestS7c12pGT5Nums, 2048),
    (wGforestS7c12pGT6Labs, wGforestS7c12pGT6Nums, 2048), (wGforestS7c12pGT7Labs,
    wGforestS7c12pGT7Nums, 2048), (wGforestS7c12pGT8Labs, wGforestS7c12pGT8Nums, 2048),
    (wGforestS7c12pGT9Labs, wGforestS7c12pGT9Nums, 2048), (wGforestS7c12pGT10Labs,
    wGforestS7c12pGT10Nums, 2048), (wGforestS7c12pGT11Labs, wGforestS7c12pGT11Nums, 2048),
    (wGforestS7c12pGT12Labs, wGforestS7c12pGT12Nums, 2048), (wGforestS7c12pGT13Labs,
    wGforestS7c12pGT13Nums, 2048), (wGforestS7c12pGT14Labs, wGforestS7c12pGT14Nums, 2048),
    (wGforestS7c12pGT15Labs, wGforestS7c12pGT15Nums, 2048), (wGforestS7c12pGT16Labs,
    wGforestS7c12pGT16Nums, 808)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGforestS7c12p_hok : octPackOk 64 wGforestS7c12pL = true :=
  OctadDense.octPackOk_of_chk 64 6 true wGforestS7c12pL _ _ 1031680 wGforestS7c12p_Lsh
      wGforestS7c12p_chk

/-- The octad integer sum. -/
theorem wGforestS7c12p_octn : octSumZ 64 true wGforestS7c12pL wGforestS7c12pW = 1031680 :=
  OctadDense.octSumZ_of_chk 64 6 true wGforestS7c12pL wGforestS7c12pW _ _ 1031680
      wGforestS7c12p_Lsh wGforestS7c12p_Wsh wGforestS7c12p_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGforestS7c12p_selfchk : OctadDense.selfOctChk 64 [(wGforestS7c12pGT0Labs,
    wGforestS7c12pGT0Nums, 2048), (wGforestS7c12pGT1Labs, wGforestS7c12pGT1Nums, 2048),
    (wGforestS7c12pGT2Labs, wGforestS7c12pGT2Nums, 2048), (wGforestS7c12pGT3Labs,
    wGforestS7c12pGT3Nums, 2048), (wGforestS7c12pGT4Labs, wGforestS7c12pGT4Nums, 2048),
    (wGforestS7c12pGT5Labs, wGforestS7c12pGT5Nums, 2048), (wGforestS7c12pGT6Labs,
    wGforestS7c12pGT6Nums, 2048), (wGforestS7c12pGT7Labs, wGforestS7c12pGT7Nums, 2048),
    (wGforestS7c12pGT8Labs, wGforestS7c12pGT8Nums, 2048), (wGforestS7c12pGT9Labs,
    wGforestS7c12pGT9Nums, 2048), (wGforestS7c12pGT10Labs, wGforestS7c12pGT10Nums, 2048),
    (wGforestS7c12pGT11Labs, wGforestS7c12pGT11Nums, 2048), (wGforestS7c12pGT12Labs,
    wGforestS7c12pGT12Nums, 2048), (wGforestS7c12pGT13Labs, wGforestS7c12pGT13Nums, 2048),
    (wGforestS7c12pGT14Labs, wGforestS7c12pGT14Nums, 2048), (wGforestS7c12pGT15Labs,
    wGforestS7c12pGT15Nums, 2048), (wGforestS7c12pGT16Labs, wGforestS7c12pGT16Nums, 808)] 515840 =
    true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGforestS7c12p_hn : wGforestS7c12pL.sden * (octSumZ 64 true wGforestS7c12pL
    wGforestS7c12pW : ℚ) / 8 =
    wGforestS7c12pW.sden * (selfOctP wGforestS7c12pW : ℚ) := by
  rw [wGforestS7c12p_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGforestS7c12pW _ 515840
      wGforestS7c12p_Wsh wGforestS7c12p_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
