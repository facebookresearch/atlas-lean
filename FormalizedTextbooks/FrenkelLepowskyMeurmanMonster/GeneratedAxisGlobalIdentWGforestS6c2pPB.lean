/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS6c2pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixthF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamFourth

/-! # Factory parts (octads) of the identification Fourth[18]- <-> Sixth[3]+ (record
gforest:S6c2+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGforestS6c2p_chk : OctadDense.octSumChk 64 6 true [(wGforestS6c2pHT0Labs,
    wGforestS6c2pHT0Nums, 2048), (wGforestS6c2pHT1Labs, wGforestS6c2pHT1Nums, 2048),
    (wGforestS6c2pHT2Labs, wGforestS6c2pHT2Nums, 2048), (wGforestS6c2pHT3Labs,
    wGforestS6c2pHT3Nums, 2048), (wGforestS6c2pHT4Labs, wGforestS6c2pHT4Nums, 2048),
    (wGforestS6c2pHT5Labs, wGforestS6c2pHT5Nums, 2048), (wGforestS6c2pHT6Labs,
    wGforestS6c2pHT6Nums, 2048), (wGforestS6c2pHT7Labs, wGforestS6c2pHT7Nums, 2048),
    (wGforestS6c2pHT8Labs, wGforestS6c2pHT8Nums, 2048), (wGforestS6c2pHT9Labs,
    wGforestS6c2pHT9Nums, 2048), (wGforestS6c2pHT10Labs, wGforestS6c2pHT10Nums, 2048),
    (wGforestS6c2pHT11Labs, wGforestS6c2pHT11Nums, 2048), (wGforestS6c2pHT12Labs,
    wGforestS6c2pHT12Nums, 2048), (wGforestS6c2pHT13Labs, wGforestS6c2pHT13Nums, 2048),
    (wGforestS6c2pHT14Labs, wGforestS6c2pHT14Nums, 1640)] [(wGforestS6c2pGT0Labs,
    wGforestS6c2pGT0Nums, 2048), (wGforestS6c2pGT1Labs, wGforestS6c2pGT1Nums, 2048),
    (wGforestS6c2pGT2Labs, wGforestS6c2pGT2Nums, 488)] 69376 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGforestS6c2p_Lsh : wGforestS6c2pL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGforestS6c2pHT0Labs, wGforestS6c2pHT0Nums, 2048), (wGforestS6c2pHT1Labs,
    wGforestS6c2pHT1Nums, 2048), (wGforestS6c2pHT2Labs, wGforestS6c2pHT2Nums, 2048),
    (wGforestS6c2pHT3Labs, wGforestS6c2pHT3Nums, 2048), (wGforestS6c2pHT4Labs,
    wGforestS6c2pHT4Nums, 2048), (wGforestS6c2pHT5Labs, wGforestS6c2pHT5Nums, 2048),
    (wGforestS6c2pHT6Labs, wGforestS6c2pHT6Nums, 2048), (wGforestS6c2pHT7Labs,
    wGforestS6c2pHT7Nums, 2048), (wGforestS6c2pHT8Labs, wGforestS6c2pHT8Nums, 2048),
    (wGforestS6c2pHT9Labs, wGforestS6c2pHT9Nums, 2048), (wGforestS6c2pHT10Labs,
    wGforestS6c2pHT10Nums, 2048), (wGforestS6c2pHT11Labs, wGforestS6c2pHT11Nums, 2048),
    (wGforestS6c2pHT12Labs, wGforestS6c2pHT12Nums, 2048), (wGforestS6c2pHT13Labs,
    wGforestS6c2pHT13Nums, 2048), (wGforestS6c2pHT14Labs, wGforestS6c2pHT14Nums, 1640)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGforestS6c2p_Wsh : wGforestS6c2pW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGforestS6c2pGT0Labs, wGforestS6c2pGT0Nums, 2048), (wGforestS6c2pGT1Labs,
    wGforestS6c2pGT1Nums, 2048), (wGforestS6c2pGT2Labs, wGforestS6c2pGT2Nums, 488)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGforestS6c2p_hok : octPackOk 64 wGforestS6c2pL = true :=
  OctadDense.octPackOk_of_chk 64 6 true wGforestS6c2pL _ _ 69376 wGforestS6c2p_Lsh wGforestS6c2p_chk

/-- The octad integer sum. -/
theorem wGforestS6c2p_octn : octSumZ 64 true wGforestS6c2pL wGforestS6c2pW = 69376 :=
  OctadDense.octSumZ_of_chk 64 6 true wGforestS6c2pL wGforestS6c2pW _ _ 69376 wGforestS6c2p_Lsh
      wGforestS6c2p_Wsh wGforestS6c2p_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGforestS6c2p_selfchk : OctadDense.selfOctChk 64 [(wGforestS6c2pGT0Labs,
    wGforestS6c2pGT0Nums, 2048), (wGforestS6c2pGT1Labs, wGforestS6c2pGT1Nums, 2048),
    (wGforestS6c2pGT2Labs, wGforestS6c2pGT2Nums, 488)] 2168 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGforestS6c2p_hn : wGforestS6c2pL.sden * (octSumZ 64 true wGforestS6c2pL wGforestS6c2pW :
    ℚ) / 8 =
    wGforestS6c2pW.sden * (selfOctP wGforestS6c2pW : ℚ) := by
  rw [wGforestS6c2p_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGforestS6c2pW _ 2168
      wGforestS6c2p_Wsh wGforestS6c2p_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
