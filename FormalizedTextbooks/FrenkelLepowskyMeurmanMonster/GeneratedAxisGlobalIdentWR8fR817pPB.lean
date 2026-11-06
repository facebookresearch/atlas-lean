/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR817pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcRootEightCF

/-! # Factory parts (octads) of the identification Root8[26]+ <-> Root8[26]+ (record r8f:R817+, e
= 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wR8fR817p_chk : OctadDense.octSumChk 64 6 true [(wR8fR817pHT0Labs, wR8fR817pHT0Nums,
    2048), (wR8fR817pHT1Labs, wR8fR817pHT1Nums, 2048), (wR8fR817pHT2Labs, wR8fR817pHT2Nums, 2048),
    (wR8fR817pHT3Labs, wR8fR817pHT3Nums, 2048), (wR8fR817pHT4Labs, wR8fR817pHT4Nums, 2048),
    (wR8fR817pHT5Labs, wR8fR817pHT5Nums, 2048), (wR8fR817pHT6Labs, wR8fR817pHT6Nums, 2048),
    (wR8fR817pHT7Labs, wR8fR817pHT7Nums, 2048), (wR8fR817pHT8Labs, wR8fR817pHT8Nums, 2048),
    (wR8fR817pHT9Labs, wR8fR817pHT9Nums, 2048), (wR8fR817pHT10Labs, wR8fR817pHT10Nums, 2048),
    (wR8fR817pHT11Labs, wR8fR817pHT11Nums, 2048), (wR8fR817pHT12Labs, wR8fR817pHT12Nums, 2048),
    (wR8fR817pHT13Labs, wR8fR817pHT13Nums, 2048), (wR8fR817pHT14Labs, wR8fR817pHT14Nums, 2048),
    (wR8fR817pHT15Labs, wR8fR817pHT15Nums, 2048), (wR8fR817pHT16Labs, wR8fR817pHT16Nums, 808)]
    [(wR8fR817pGT0Labs, wR8fR817pGT0Nums, 2048), (wR8fR817pGT1Labs, wR8fR817pGT1Nums, 2048),
    (wR8fR817pGT2Labs, wR8fR817pGT2Nums, 2048), (wR8fR817pGT3Labs, wR8fR817pGT3Nums, 2048),
    (wR8fR817pGT4Labs, wR8fR817pGT4Nums, 2048), (wR8fR817pGT5Labs, wR8fR817pGT5Nums, 2048),
    (wR8fR817pGT6Labs, wR8fR817pGT6Nums, 2048), (wR8fR817pGT7Labs, wR8fR817pGT7Nums, 2048),
    (wR8fR817pGT8Labs, wR8fR817pGT8Nums, 2048), (wR8fR817pGT9Labs, wR8fR817pGT9Nums, 2048),
    (wR8fR817pGT10Labs, wR8fR817pGT10Nums, 2048), (wR8fR817pGT11Labs, wR8fR817pGT11Nums, 2048),
    (wR8fR817pGT12Labs, wR8fR817pGT12Nums, 2048), (wR8fR817pGT13Labs, wR8fR817pGT13Nums, 2048),
    (wR8fR817pGT14Labs, wR8fR817pGT14Nums, 2048), (wR8fR817pGT15Labs, wR8fR817pGT15Nums, 2048),
    (wR8fR817pGT16Labs, wR8fR817pGT16Nums, 808)] 4115968 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wR8fR817p_Lsh : wR8fR817pL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR817pHT0Labs, wR8fR817pHT0Nums, 2048), (wR8fR817pHT1Labs, wR8fR817pHT1Nums, 2048),
    (wR8fR817pHT2Labs, wR8fR817pHT2Nums, 2048), (wR8fR817pHT3Labs, wR8fR817pHT3Nums, 2048),
    (wR8fR817pHT4Labs, wR8fR817pHT4Nums, 2048), (wR8fR817pHT5Labs, wR8fR817pHT5Nums, 2048),
    (wR8fR817pHT6Labs, wR8fR817pHT6Nums, 2048), (wR8fR817pHT7Labs, wR8fR817pHT7Nums, 2048),
    (wR8fR817pHT8Labs, wR8fR817pHT8Nums, 2048), (wR8fR817pHT9Labs, wR8fR817pHT9Nums, 2048),
    (wR8fR817pHT10Labs, wR8fR817pHT10Nums, 2048), (wR8fR817pHT11Labs, wR8fR817pHT11Nums, 2048),
    (wR8fR817pHT12Labs, wR8fR817pHT12Nums, 2048), (wR8fR817pHT13Labs, wR8fR817pHT13Nums, 2048),
    (wR8fR817pHT14Labs, wR8fR817pHT14Nums, 2048), (wR8fR817pHT15Labs, wR8fR817pHT15Nums, 2048),
    (wR8fR817pHT16Labs, wR8fR817pHT16Nums, 808)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wR8fR817p_Wsh : wR8fR817pW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR817pGT0Labs, wR8fR817pGT0Nums, 2048), (wR8fR817pGT1Labs, wR8fR817pGT1Nums, 2048),
    (wR8fR817pGT2Labs, wR8fR817pGT2Nums, 2048), (wR8fR817pGT3Labs, wR8fR817pGT3Nums, 2048),
    (wR8fR817pGT4Labs, wR8fR817pGT4Nums, 2048), (wR8fR817pGT5Labs, wR8fR817pGT5Nums, 2048),
    (wR8fR817pGT6Labs, wR8fR817pGT6Nums, 2048), (wR8fR817pGT7Labs, wR8fR817pGT7Nums, 2048),
    (wR8fR817pGT8Labs, wR8fR817pGT8Nums, 2048), (wR8fR817pGT9Labs, wR8fR817pGT9Nums, 2048),
    (wR8fR817pGT10Labs, wR8fR817pGT10Nums, 2048), (wR8fR817pGT11Labs, wR8fR817pGT11Nums, 2048),
    (wR8fR817pGT12Labs, wR8fR817pGT12Nums, 2048), (wR8fR817pGT13Labs, wR8fR817pGT13Nums, 2048),
    (wR8fR817pGT14Labs, wR8fR817pGT14Nums, 2048), (wR8fR817pGT15Labs, wR8fR817pGT15Nums, 2048),
    (wR8fR817pGT16Labs, wR8fR817pGT16Nums, 808)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wR8fR817p_hok : octPackOk 64 wR8fR817pL = true :=
  OctadDense.octPackOk_of_chk 64 6 true wR8fR817pL _ _ 4115968 wR8fR817p_Lsh wR8fR817p_chk

/-- The octad integer sum. -/
theorem wR8fR817p_octn : octSumZ 64 true wR8fR817pL wR8fR817pW = 4115968 :=
  OctadDense.octSumZ_of_chk 64 6 true wR8fR817pL wR8fR817pW _ _ 4115968 wR8fR817p_Lsh
      wR8fR817p_Wsh wR8fR817p_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wR8fR817p_selfchk : OctadDense.selfOctChk 64 [(wR8fR817pGT0Labs, wR8fR817pGT0Nums, 2048),
    (wR8fR817pGT1Labs, wR8fR817pGT1Nums, 2048), (wR8fR817pGT2Labs, wR8fR817pGT2Nums, 2048),
    (wR8fR817pGT3Labs, wR8fR817pGT3Nums, 2048), (wR8fR817pGT4Labs, wR8fR817pGT4Nums, 2048),
    (wR8fR817pGT5Labs, wR8fR817pGT5Nums, 2048), (wR8fR817pGT6Labs, wR8fR817pGT6Nums, 2048),
    (wR8fR817pGT7Labs, wR8fR817pGT7Nums, 2048), (wR8fR817pGT8Labs, wR8fR817pGT8Nums, 2048),
    (wR8fR817pGT9Labs, wR8fR817pGT9Nums, 2048), (wR8fR817pGT10Labs, wR8fR817pGT10Nums, 2048),
    (wR8fR817pGT11Labs, wR8fR817pGT11Nums, 2048), (wR8fR817pGT12Labs, wR8fR817pGT12Nums, 2048),
    (wR8fR817pGT13Labs, wR8fR817pGT13Nums, 2048), (wR8fR817pGT14Labs, wR8fR817pGT14Nums, 2048),
    (wR8fR817pGT15Labs, wR8fR817pGT15Nums, 2048), (wR8fR817pGT16Labs, wR8fR817pGT16Nums, 808)]
    514496 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wR8fR817p_hn : wR8fR817pL.sden * (octSumZ 64 true wR8fR817pL wR8fR817pW : ℚ) / 8 =
    wR8fR817pW.sden * (selfOctP wR8fR817pW : ℚ) := by
  rw [wR8fR817p_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wR8fR817pW _ 514496 wR8fR817p_Wsh
      wR8fR817p_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
