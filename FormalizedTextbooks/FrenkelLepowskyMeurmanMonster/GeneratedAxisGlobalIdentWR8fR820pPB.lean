/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR820pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcRootEightCF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamFourth

/-! # Factory parts (octads) of the identification Fourth[10]+ <-> Root8[25]+ (record r8f:R820+, e
= 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wR8fR820p_chk : OctadDense.octSumChk 64 6 true [(wR8fR820pHT0Labs, wR8fR820pHT0Nums,
    2048), (wR8fR820pHT1Labs, wR8fR820pHT1Nums, 2048), (wR8fR820pHT2Labs, wR8fR820pHT2Nums, 2048),
    (wR8fR820pHT3Labs, wR8fR820pHT3Nums, 2048), (wR8fR820pHT4Labs, wR8fR820pHT4Nums, 2048),
    (wR8fR820pHT5Labs, wR8fR820pHT5Nums, 2048), (wR8fR820pHT6Labs, wR8fR820pHT6Nums, 2048),
    (wR8fR820pHT7Labs, wR8fR820pHT7Nums, 2048), (wR8fR820pHT8Labs, wR8fR820pHT8Nums, 2048),
    (wR8fR820pHT9Labs, wR8fR820pHT9Nums, 2048), (wR8fR820pHT10Labs, wR8fR820pHT10Nums, 2048),
    (wR8fR820pHT11Labs, wR8fR820pHT11Nums, 2048), (wR8fR820pHT12Labs, wR8fR820pHT12Nums, 2048),
    (wR8fR820pHT13Labs, wR8fR820pHT13Nums, 2048), (wR8fR820pHT14Labs, wR8fR820pHT14Nums, 2048),
    (wR8fR820pHT15Labs, wR8fR820pHT15Nums, 2048), (wR8fR820pHT16Labs, wR8fR820pHT16Nums, 808)]
    [(wR8fR820pGT0Labs, wR8fR820pGT0Nums, 2048), (wR8fR820pGT1Labs, wR8fR820pGT1Nums, 2048),
    (wR8fR820pGT2Labs, wR8fR820pGT2Nums, 488)] 272384 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wR8fR820p_Lsh : wR8fR820pL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR820pHT0Labs, wR8fR820pHT0Nums, 2048), (wR8fR820pHT1Labs, wR8fR820pHT1Nums, 2048),
    (wR8fR820pHT2Labs, wR8fR820pHT2Nums, 2048), (wR8fR820pHT3Labs, wR8fR820pHT3Nums, 2048),
    (wR8fR820pHT4Labs, wR8fR820pHT4Nums, 2048), (wR8fR820pHT5Labs, wR8fR820pHT5Nums, 2048),
    (wR8fR820pHT6Labs, wR8fR820pHT6Nums, 2048), (wR8fR820pHT7Labs, wR8fR820pHT7Nums, 2048),
    (wR8fR820pHT8Labs, wR8fR820pHT8Nums, 2048), (wR8fR820pHT9Labs, wR8fR820pHT9Nums, 2048),
    (wR8fR820pHT10Labs, wR8fR820pHT10Nums, 2048), (wR8fR820pHT11Labs, wR8fR820pHT11Nums, 2048),
    (wR8fR820pHT12Labs, wR8fR820pHT12Nums, 2048), (wR8fR820pHT13Labs, wR8fR820pHT13Nums, 2048),
    (wR8fR820pHT14Labs, wR8fR820pHT14Nums, 2048), (wR8fR820pHT15Labs, wR8fR820pHT15Nums, 2048),
    (wR8fR820pHT16Labs, wR8fR820pHT16Nums, 808)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wR8fR820p_Wsh : wR8fR820pW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR820pGT0Labs, wR8fR820pGT0Nums, 2048), (wR8fR820pGT1Labs, wR8fR820pGT1Nums, 2048),
    (wR8fR820pGT2Labs, wR8fR820pGT2Nums, 488)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wR8fR820p_hok : octPackOk 64 wR8fR820pL = true :=
  OctadDense.octPackOk_of_chk 64 6 true wR8fR820pL _ _ 272384 wR8fR820p_Lsh wR8fR820p_chk

/-- The octad integer sum. -/
theorem wR8fR820p_octn : octSumZ 64 true wR8fR820pL wR8fR820pW = 272384 :=
  OctadDense.octSumZ_of_chk 64 6 true wR8fR820pL wR8fR820pW _ _ 272384 wR8fR820p_Lsh wR8fR820p_Wsh
      wR8fR820p_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wR8fR820p_selfchk : OctadDense.selfOctChk 64 [(wR8fR820pGT0Labs, wR8fR820pGT0Nums, 2048),
    (wR8fR820pGT1Labs, wR8fR820pGT1Nums, 2048), (wR8fR820pGT2Labs, wR8fR820pGT2Nums, 488)] 2128 =
    true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wR8fR820p_hn : wR8fR820pL.sden * (octSumZ 64 true wR8fR820pL wR8fR820pW : ℚ) / 8 =
    wR8fR820pW.sden * (selfOctP wR8fR820pW : ℚ) := by
  rw [wR8fR820p_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wR8fR820pW _ 2128 wR8fR820p_Wsh
      wR8fR820p_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
