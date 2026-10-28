/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR813pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcRootEightCF

/-! # Factory parts (octads) of the identification Root8[7]+ <-> Root8[7]+ (record r8f:R813+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wR8fR813p_chk : OctadDense.octSumChk 64 6 true [(wR8fR813pHT0Labs, wR8fR813pHT0Nums,
    2048), (wR8fR813pHT1Labs, wR8fR813pHT1Nums, 2048), (wR8fR813pHT2Labs, wR8fR813pHT2Nums, 2048),
    (wR8fR813pHT3Labs, wR8fR813pHT3Nums, 2048), (wR8fR813pHT4Labs, wR8fR813pHT4Nums, 2048),
    (wR8fR813pHT5Labs, wR8fR813pHT5Nums, 2048), (wR8fR813pHT6Labs, wR8fR813pHT6Nums, 2048),
    (wR8fR813pHT7Labs, wR8fR813pHT7Nums, 2048), (wR8fR813pHT8Labs, wR8fR813pHT8Nums, 2048),
    (wR8fR813pHT9Labs, wR8fR813pHT9Nums, 2048), (wR8fR813pHT10Labs, wR8fR813pHT10Nums, 2048),
    (wR8fR813pHT11Labs, wR8fR813pHT11Nums, 2048), (wR8fR813pHT12Labs, wR8fR813pHT12Nums, 2048),
    (wR8fR813pHT13Labs, wR8fR813pHT13Nums, 2048), (wR8fR813pHT14Labs, wR8fR813pHT14Nums, 2048),
    (wR8fR813pHT15Labs, wR8fR813pHT15Nums, 2048), (wR8fR813pHT16Labs, wR8fR813pHT16Nums, 808)]
    [(wR8fR813pGT0Labs, wR8fR813pGT0Nums, 2048), (wR8fR813pGT1Labs, wR8fR813pGT1Nums, 2048),
    (wR8fR813pGT2Labs, wR8fR813pGT2Nums, 2048), (wR8fR813pGT3Labs, wR8fR813pGT3Nums, 2048),
    (wR8fR813pGT4Labs, wR8fR813pGT4Nums, 2048), (wR8fR813pGT5Labs, wR8fR813pGT5Nums, 2048),
    (wR8fR813pGT6Labs, wR8fR813pGT6Nums, 2048), (wR8fR813pGT7Labs, wR8fR813pGT7Nums, 2048),
    (wR8fR813pGT8Labs, wR8fR813pGT8Nums, 2048), (wR8fR813pGT9Labs, wR8fR813pGT9Nums, 2048),
    (wR8fR813pGT10Labs, wR8fR813pGT10Nums, 2048), (wR8fR813pGT11Labs, wR8fR813pGT11Nums, 2048),
    (wR8fR813pGT12Labs, wR8fR813pGT12Nums, 2048), (wR8fR813pGT13Labs, wR8fR813pGT13Nums, 2048),
    (wR8fR813pGT14Labs, wR8fR813pGT14Nums, 2048), (wR8fR813pGT15Labs, wR8fR813pGT15Nums, 2048),
    (wR8fR813pGT16Labs, wR8fR813pGT16Nums, 808)] 4120064 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wR8fR813p_Lsh : wR8fR813pL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR813pHT0Labs, wR8fR813pHT0Nums, 2048), (wR8fR813pHT1Labs, wR8fR813pHT1Nums, 2048),
    (wR8fR813pHT2Labs, wR8fR813pHT2Nums, 2048), (wR8fR813pHT3Labs, wR8fR813pHT3Nums, 2048),
    (wR8fR813pHT4Labs, wR8fR813pHT4Nums, 2048), (wR8fR813pHT5Labs, wR8fR813pHT5Nums, 2048),
    (wR8fR813pHT6Labs, wR8fR813pHT6Nums, 2048), (wR8fR813pHT7Labs, wR8fR813pHT7Nums, 2048),
    (wR8fR813pHT8Labs, wR8fR813pHT8Nums, 2048), (wR8fR813pHT9Labs, wR8fR813pHT9Nums, 2048),
    (wR8fR813pHT10Labs, wR8fR813pHT10Nums, 2048), (wR8fR813pHT11Labs, wR8fR813pHT11Nums, 2048),
    (wR8fR813pHT12Labs, wR8fR813pHT12Nums, 2048), (wR8fR813pHT13Labs, wR8fR813pHT13Nums, 2048),
    (wR8fR813pHT14Labs, wR8fR813pHT14Nums, 2048), (wR8fR813pHT15Labs, wR8fR813pHT15Nums, 2048),
    (wR8fR813pHT16Labs, wR8fR813pHT16Nums, 808)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wR8fR813p_Wsh : wR8fR813pW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR813pGT0Labs, wR8fR813pGT0Nums, 2048), (wR8fR813pGT1Labs, wR8fR813pGT1Nums, 2048),
    (wR8fR813pGT2Labs, wR8fR813pGT2Nums, 2048), (wR8fR813pGT3Labs, wR8fR813pGT3Nums, 2048),
    (wR8fR813pGT4Labs, wR8fR813pGT4Nums, 2048), (wR8fR813pGT5Labs, wR8fR813pGT5Nums, 2048),
    (wR8fR813pGT6Labs, wR8fR813pGT6Nums, 2048), (wR8fR813pGT7Labs, wR8fR813pGT7Nums, 2048),
    (wR8fR813pGT8Labs, wR8fR813pGT8Nums, 2048), (wR8fR813pGT9Labs, wR8fR813pGT9Nums, 2048),
    (wR8fR813pGT10Labs, wR8fR813pGT10Nums, 2048), (wR8fR813pGT11Labs, wR8fR813pGT11Nums, 2048),
    (wR8fR813pGT12Labs, wR8fR813pGT12Nums, 2048), (wR8fR813pGT13Labs, wR8fR813pGT13Nums, 2048),
    (wR8fR813pGT14Labs, wR8fR813pGT14Nums, 2048), (wR8fR813pGT15Labs, wR8fR813pGT15Nums, 2048),
    (wR8fR813pGT16Labs, wR8fR813pGT16Nums, 808)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wR8fR813p_hok : octPackOk 64 wR8fR813pL = true :=
  OctadDense.octPackOk_of_chk 64 6 true wR8fR813pL _ _ 4120064 wR8fR813p_Lsh wR8fR813p_chk

/-- The octad integer sum. -/
theorem wR8fR813p_octn : octSumZ 64 true wR8fR813pL wR8fR813pW = 4120064 :=
  OctadDense.octSumZ_of_chk 64 6 true wR8fR813pL wR8fR813pW _ _ 4120064 wR8fR813p_Lsh
      wR8fR813p_Wsh wR8fR813p_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wR8fR813p_selfchk : OctadDense.selfOctChk 64 [(wR8fR813pGT0Labs, wR8fR813pGT0Nums, 2048),
    (wR8fR813pGT1Labs, wR8fR813pGT1Nums, 2048), (wR8fR813pGT2Labs, wR8fR813pGT2Nums, 2048),
    (wR8fR813pGT3Labs, wR8fR813pGT3Nums, 2048), (wR8fR813pGT4Labs, wR8fR813pGT4Nums, 2048),
    (wR8fR813pGT5Labs, wR8fR813pGT5Nums, 2048), (wR8fR813pGT6Labs, wR8fR813pGT6Nums, 2048),
    (wR8fR813pGT7Labs, wR8fR813pGT7Nums, 2048), (wR8fR813pGT8Labs, wR8fR813pGT8Nums, 2048),
    (wR8fR813pGT9Labs, wR8fR813pGT9Nums, 2048), (wR8fR813pGT10Labs, wR8fR813pGT10Nums, 2048),
    (wR8fR813pGT11Labs, wR8fR813pGT11Nums, 2048), (wR8fR813pGT12Labs, wR8fR813pGT12Nums, 2048),
    (wR8fR813pGT13Labs, wR8fR813pGT13Nums, 2048), (wR8fR813pGT14Labs, wR8fR813pGT14Nums, 2048),
    (wR8fR813pGT15Labs, wR8fR813pGT15Nums, 2048), (wR8fR813pGT16Labs, wR8fR813pGT16Nums, 808)]
    515008 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wR8fR813p_hn : wR8fR813pL.sden * (octSumZ 64 true wR8fR813pL wR8fR813pW : ℚ) / 8 =
    wR8fR813pW.sden * (selfOctP wR8fR813pW : ℚ) := by
  rw [wR8fR813p_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wR8fR813pW _ 515008 wR8fR813p_Wsh
      wR8fR813p_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
