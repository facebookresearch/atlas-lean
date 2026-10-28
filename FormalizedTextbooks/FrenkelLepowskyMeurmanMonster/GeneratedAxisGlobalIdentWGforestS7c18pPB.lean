/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c18pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamFourth

/-! # Factory parts (octads) of the identification Fourth[13]- <-> Seventh[27]+ (record
gforest:S7c18+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGforestS7c18p_chk : OctadDense.octSumChk 64 5 true [(wGforestS7c18pHT0Labs,
    wGforestS7c18pHT0Nums, 2048), (wGforestS7c18pHT1Labs, wGforestS7c18pHT1Nums, 2048),
    (wGforestS7c18pHT2Labs, wGforestS7c18pHT2Nums, 2048), (wGforestS7c18pHT3Labs,
    wGforestS7c18pHT3Nums, 2048), (wGforestS7c18pHT4Labs, wGforestS7c18pHT4Nums, 2048),
    (wGforestS7c18pHT5Labs, wGforestS7c18pHT5Nums, 2048), (wGforestS7c18pHT6Labs,
    wGforestS7c18pHT6Nums, 2048), (wGforestS7c18pHT7Labs, wGforestS7c18pHT7Nums, 2048),
    (wGforestS7c18pHT8Labs, wGforestS7c18pHT8Nums, 2048), (wGforestS7c18pHT9Labs,
    wGforestS7c18pHT9Nums, 2048), (wGforestS7c18pHT10Labs, wGforestS7c18pHT10Nums, 2048),
    (wGforestS7c18pHT11Labs, wGforestS7c18pHT11Nums, 2048), (wGforestS7c18pHT12Labs,
    wGforestS7c18pHT12Nums, 2048), (wGforestS7c18pHT13Labs, wGforestS7c18pHT13Nums, 1000)]
    [(wGforestS7c18pGT0Labs, wGforestS7c18pGT0Nums, 2048), (wGforestS7c18pGT1Labs,
    wGforestS7c18pGT1Nums, 2048), (wGforestS7c18pGT2Labs, wGforestS7c18pGT2Nums, 488)] 71936 =
    true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGforestS7c18p_Lsh : wGforestS7c18pL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGforestS7c18pHT0Labs, wGforestS7c18pHT0Nums, 2048), (wGforestS7c18pHT1Labs,
    wGforestS7c18pHT1Nums, 2048), (wGforestS7c18pHT2Labs, wGforestS7c18pHT2Nums, 2048),
    (wGforestS7c18pHT3Labs, wGforestS7c18pHT3Nums, 2048), (wGforestS7c18pHT4Labs,
    wGforestS7c18pHT4Nums, 2048), (wGforestS7c18pHT5Labs, wGforestS7c18pHT5Nums, 2048),
    (wGforestS7c18pHT6Labs, wGforestS7c18pHT6Nums, 2048), (wGforestS7c18pHT7Labs,
    wGforestS7c18pHT7Nums, 2048), (wGforestS7c18pHT8Labs, wGforestS7c18pHT8Nums, 2048),
    (wGforestS7c18pHT9Labs, wGforestS7c18pHT9Nums, 2048), (wGforestS7c18pHT10Labs,
    wGforestS7c18pHT10Nums, 2048), (wGforestS7c18pHT11Labs, wGforestS7c18pHT11Nums, 2048),
    (wGforestS7c18pHT12Labs, wGforestS7c18pHT12Nums, 2048), (wGforestS7c18pHT13Labs,
    wGforestS7c18pHT13Nums, 1000)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGforestS7c18p_Wsh : wGforestS7c18pW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGforestS7c18pGT0Labs, wGforestS7c18pGT0Nums, 2048), (wGforestS7c18pGT1Labs,
    wGforestS7c18pGT1Nums, 2048), (wGforestS7c18pGT2Labs, wGforestS7c18pGT2Nums, 488)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGforestS7c18p_hok : octPackOk 64 wGforestS7c18pL = true :=
  OctadDense.octPackOk_of_chk 64 5 true wGforestS7c18pL _ _ 71936 wGforestS7c18p_Lsh
      wGforestS7c18p_chk

/-- The octad integer sum. -/
theorem wGforestS7c18p_octn : octSumZ 64 true wGforestS7c18pL wGforestS7c18pW = 71936 :=
  OctadDense.octSumZ_of_chk 64 5 true wGforestS7c18pL wGforestS7c18pW _ _ 71936 wGforestS7c18p_Lsh
      wGforestS7c18p_Wsh wGforestS7c18p_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGforestS7c18p_selfchk : OctadDense.selfOctChk 64 [(wGforestS7c18pGT0Labs,
    wGforestS7c18pGT0Nums, 2048), (wGforestS7c18pGT1Labs, wGforestS7c18pGT1Nums, 2048),
    (wGforestS7c18pGT2Labs, wGforestS7c18pGT2Nums, 488)] 2248 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGforestS7c18p_hn : wGforestS7c18pL.sden * (octSumZ 64 true wGforestS7c18pL
    wGforestS7c18pW : ℚ) / 8 =
    wGforestS7c18pW.sden * (selfOctP wGforestS7c18pW : ℚ) := by
  rw [wGforestS7c18p_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGforestS7c18pW _ 2248
      wGforestS7c18p_Wsh wGforestS7c18p_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
