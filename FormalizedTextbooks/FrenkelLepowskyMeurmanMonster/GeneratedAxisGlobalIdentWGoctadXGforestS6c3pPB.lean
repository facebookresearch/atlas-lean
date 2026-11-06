/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS6c3pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixthF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octads) of the identification Sixth[6]+ <-> Tenth[81]- (record gforest:S6c3+,
e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGoctadXGforestS6c3p_chk : OctadDense.octSumChk 64 7 true [(wGoctadXGforestS6c3pHT0Labs,
    wGoctadXGforestS6c3pHT0Nums, 2048), (wGoctadXGforestS6c3pHT1Labs, wGoctadXGforestS6c3pHT1Nums,
    2048), (wGoctadXGforestS6c3pHT2Labs, wGoctadXGforestS6c3pHT2Nums, 2048),
    (wGoctadXGforestS6c3pHT3Labs, wGoctadXGforestS6c3pHT3Nums, 2048),
    (wGoctadXGforestS6c3pHT4Labs, wGoctadXGforestS6c3pHT4Nums, 2048),
    (wGoctadXGforestS6c3pHT5Labs, wGoctadXGforestS6c3pHT5Nums, 2048),
    (wGoctadXGforestS6c3pHT6Labs, wGoctadXGforestS6c3pHT6Nums, 2048),
    (wGoctadXGforestS6c3pHT7Labs, wGoctadXGforestS6c3pHT7Nums, 2048),
    (wGoctadXGforestS6c3pHT8Labs, wGoctadXGforestS6c3pHT8Nums, 2048),
    (wGoctadXGforestS6c3pHT9Labs, wGoctadXGforestS6c3pHT9Nums, 2048),
    (wGoctadXGforestS6c3pHT10Labs, wGoctadXGforestS6c3pHT10Nums, 2048),
    (wGoctadXGforestS6c3pHT11Labs, wGoctadXGforestS6c3pHT11Nums, 2048),
    (wGoctadXGforestS6c3pHT12Labs, wGoctadXGforestS6c3pHT12Nums, 2048),
    (wGoctadXGforestS6c3pHT13Labs, wGoctadXGforestS6c3pHT13Nums, 2048),
    (wGoctadXGforestS6c3pHT14Labs, wGoctadXGforestS6c3pHT14Nums, 1640)]
    [(wGoctadXGforestS6c3pGT0Labs, wGoctadXGforestS6c3pGT0Nums, 2048),
    (wGoctadXGforestS6c3pGT1Labs, wGoctadXGforestS6c3pGT1Nums, 2048),
    (wGoctadXGforestS6c3pGT2Labs, wGoctadXGforestS6c3pGT2Nums, 2048),
    (wGoctadXGforestS6c3pGT3Labs, wGoctadXGforestS6c3pGT3Nums, 2048),
    (wGoctadXGforestS6c3pGT4Labs, wGoctadXGforestS6c3pGT4Nums, 2048),
    (wGoctadXGforestS6c3pGT5Labs, wGoctadXGforestS6c3pGT5Nums, 2048),
    (wGoctadXGforestS6c3pGT6Labs, wGoctadXGforestS6c3pGT6Nums, 2048),
    (wGoctadXGforestS6c3pGT7Labs, wGoctadXGforestS6c3pGT7Nums, 2048),
    (wGoctadXGforestS6c3pGT8Labs, wGoctadXGforestS6c3pGT8Nums, 2048),
    (wGoctadXGforestS6c3pGT9Labs, wGoctadXGforestS6c3pGT9Nums, 2048),
    (wGoctadXGforestS6c3pGT10Labs, wGoctadXGforestS6c3pGT10Nums, 2048),
    (wGoctadXGforestS6c3pGT11Labs, wGoctadXGforestS6c3pGT11Nums, 2048),
    (wGoctadXGforestS6c3pGT12Labs, wGoctadXGforestS6c3pGT12Nums, 2048),
    (wGoctadXGforestS6c3pGT13Labs, wGoctadXGforestS6c3pGT13Nums, 2048),
    (wGoctadXGforestS6c3pGT14Labs, wGoctadXGforestS6c3pGT14Nums, 2048),
    (wGoctadXGforestS6c3pGT15Labs, wGoctadXGforestS6c3pGT15Nums, 2048),
    (wGoctadXGforestS6c3pGT16Labs, wGoctadXGforestS6c3pGT16Nums, 2048),
    (wGoctadXGforestS6c3pGT17Labs, wGoctadXGforestS6c3pGT17Nums, 2048),
    (wGoctadXGforestS6c3pGT18Labs, wGoctadXGforestS6c3pGT18Nums, 2048),
    (wGoctadXGforestS6c3pGT19Labs, wGoctadXGforestS6c3pGT19Nums, 2048),
    (wGoctadXGforestS6c3pGT20Labs, wGoctadXGforestS6c3pGT20Nums, 2048),
    (wGoctadXGforestS6c3pGT21Labs, wGoctadXGforestS6c3pGT21Nums, 2048),
    (wGoctadXGforestS6c3pGT22Labs, wGoctadXGforestS6c3pGT22Nums, 1026)] 1006976 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGoctadXGforestS6c3p_Lsh : wGoctadXGforestS6c3pL.sh = ShortData.ofList
    (OctadDense.octChunkTerms [(wGoctadXGforestS6c3pHT0Labs, wGoctadXGforestS6c3pHT0Nums, 2048),
    (wGoctadXGforestS6c3pHT1Labs, wGoctadXGforestS6c3pHT1Nums, 2048),
    (wGoctadXGforestS6c3pHT2Labs, wGoctadXGforestS6c3pHT2Nums, 2048),
    (wGoctadXGforestS6c3pHT3Labs, wGoctadXGforestS6c3pHT3Nums, 2048),
    (wGoctadXGforestS6c3pHT4Labs, wGoctadXGforestS6c3pHT4Nums, 2048),
    (wGoctadXGforestS6c3pHT5Labs, wGoctadXGforestS6c3pHT5Nums, 2048),
    (wGoctadXGforestS6c3pHT6Labs, wGoctadXGforestS6c3pHT6Nums, 2048),
    (wGoctadXGforestS6c3pHT7Labs, wGoctadXGforestS6c3pHT7Nums, 2048),
    (wGoctadXGforestS6c3pHT8Labs, wGoctadXGforestS6c3pHT8Nums, 2048),
    (wGoctadXGforestS6c3pHT9Labs, wGoctadXGforestS6c3pHT9Nums, 2048),
    (wGoctadXGforestS6c3pHT10Labs, wGoctadXGforestS6c3pHT10Nums, 2048),
    (wGoctadXGforestS6c3pHT11Labs, wGoctadXGforestS6c3pHT11Nums, 2048),
    (wGoctadXGforestS6c3pHT12Labs, wGoctadXGforestS6c3pHT12Nums, 2048),
    (wGoctadXGforestS6c3pHT13Labs, wGoctadXGforestS6c3pHT13Nums, 2048),
    (wGoctadXGforestS6c3pHT14Labs, wGoctadXGforestS6c3pHT14Nums, 1640)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGoctadXGforestS6c3p_Wsh : wGoctadXGforestS6c3pW.sh = ShortData.ofList
    (OctadDense.octChunkTerms [(wGoctadXGforestS6c3pGT0Labs, wGoctadXGforestS6c3pGT0Nums, 2048),
    (wGoctadXGforestS6c3pGT1Labs, wGoctadXGforestS6c3pGT1Nums, 2048),
    (wGoctadXGforestS6c3pGT2Labs, wGoctadXGforestS6c3pGT2Nums, 2048),
    (wGoctadXGforestS6c3pGT3Labs, wGoctadXGforestS6c3pGT3Nums, 2048),
    (wGoctadXGforestS6c3pGT4Labs, wGoctadXGforestS6c3pGT4Nums, 2048),
    (wGoctadXGforestS6c3pGT5Labs, wGoctadXGforestS6c3pGT5Nums, 2048),
    (wGoctadXGforestS6c3pGT6Labs, wGoctadXGforestS6c3pGT6Nums, 2048),
    (wGoctadXGforestS6c3pGT7Labs, wGoctadXGforestS6c3pGT7Nums, 2048),
    (wGoctadXGforestS6c3pGT8Labs, wGoctadXGforestS6c3pGT8Nums, 2048),
    (wGoctadXGforestS6c3pGT9Labs, wGoctadXGforestS6c3pGT9Nums, 2048),
    (wGoctadXGforestS6c3pGT10Labs, wGoctadXGforestS6c3pGT10Nums, 2048),
    (wGoctadXGforestS6c3pGT11Labs, wGoctadXGforestS6c3pGT11Nums, 2048),
    (wGoctadXGforestS6c3pGT12Labs, wGoctadXGforestS6c3pGT12Nums, 2048),
    (wGoctadXGforestS6c3pGT13Labs, wGoctadXGforestS6c3pGT13Nums, 2048),
    (wGoctadXGforestS6c3pGT14Labs, wGoctadXGforestS6c3pGT14Nums, 2048),
    (wGoctadXGforestS6c3pGT15Labs, wGoctadXGforestS6c3pGT15Nums, 2048),
    (wGoctadXGforestS6c3pGT16Labs, wGoctadXGforestS6c3pGT16Nums, 2048),
    (wGoctadXGforestS6c3pGT17Labs, wGoctadXGforestS6c3pGT17Nums, 2048),
    (wGoctadXGforestS6c3pGT18Labs, wGoctadXGforestS6c3pGT18Nums, 2048),
    (wGoctadXGforestS6c3pGT19Labs, wGoctadXGforestS6c3pGT19Nums, 2048),
    (wGoctadXGforestS6c3pGT20Labs, wGoctadXGforestS6c3pGT20Nums, 2048),
    (wGoctadXGforestS6c3pGT21Labs, wGoctadXGforestS6c3pGT21Nums, 2048),
    (wGoctadXGforestS6c3pGT22Labs, wGoctadXGforestS6c3pGT22Nums, 1026)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGoctadXGforestS6c3p_hok : octPackOk 64 wGoctadXGforestS6c3pL = true :=
  OctadDense.octPackOk_of_chk 64 7 true wGoctadXGforestS6c3pL _ _ 1006976 wGoctadXGforestS6c3p_Lsh
      wGoctadXGforestS6c3p_chk

/-- The octad integer sum. -/
theorem wGoctadXGforestS6c3p_octn : octSumZ 64 true wGoctadXGforestS6c3pL wGoctadXGforestS6c3pW =
    1006976 :=
  OctadDense.octSumZ_of_chk 64 7 true wGoctadXGforestS6c3pL wGoctadXGforestS6c3pW _ _ 1006976
      wGoctadXGforestS6c3p_Lsh wGoctadXGforestS6c3p_Wsh wGoctadXGforestS6c3p_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGoctadXGforestS6c3p_selfchk : OctadDense.selfOctChk 64 [(wGoctadXGforestS6c3pGT0Labs,
    wGoctadXGforestS6c3pGT0Nums, 2048), (wGoctadXGforestS6c3pGT1Labs, wGoctadXGforestS6c3pGT1Nums,
    2048), (wGoctadXGforestS6c3pGT2Labs, wGoctadXGforestS6c3pGT2Nums, 2048),
    (wGoctadXGforestS6c3pGT3Labs, wGoctadXGforestS6c3pGT3Nums, 2048),
    (wGoctadXGforestS6c3pGT4Labs, wGoctadXGforestS6c3pGT4Nums, 2048),
    (wGoctadXGforestS6c3pGT5Labs, wGoctadXGforestS6c3pGT5Nums, 2048),
    (wGoctadXGforestS6c3pGT6Labs, wGoctadXGforestS6c3pGT6Nums, 2048),
    (wGoctadXGforestS6c3pGT7Labs, wGoctadXGforestS6c3pGT7Nums, 2048),
    (wGoctadXGforestS6c3pGT8Labs, wGoctadXGforestS6c3pGT8Nums, 2048),
    (wGoctadXGforestS6c3pGT9Labs, wGoctadXGforestS6c3pGT9Nums, 2048),
    (wGoctadXGforestS6c3pGT10Labs, wGoctadXGforestS6c3pGT10Nums, 2048),
    (wGoctadXGforestS6c3pGT11Labs, wGoctadXGforestS6c3pGT11Nums, 2048),
    (wGoctadXGforestS6c3pGT12Labs, wGoctadXGforestS6c3pGT12Nums, 2048),
    (wGoctadXGforestS6c3pGT13Labs, wGoctadXGforestS6c3pGT13Nums, 2048),
    (wGoctadXGforestS6c3pGT14Labs, wGoctadXGforestS6c3pGT14Nums, 2048),
    (wGoctadXGforestS6c3pGT15Labs, wGoctadXGforestS6c3pGT15Nums, 2048),
    (wGoctadXGforestS6c3pGT16Labs, wGoctadXGforestS6c3pGT16Nums, 2048),
    (wGoctadXGforestS6c3pGT17Labs, wGoctadXGforestS6c3pGT17Nums, 2048),
    (wGoctadXGforestS6c3pGT18Labs, wGoctadXGforestS6c3pGT18Nums, 2048),
    (wGoctadXGforestS6c3pGT19Labs, wGoctadXGforestS6c3pGT19Nums, 2048),
    (wGoctadXGforestS6c3pGT20Labs, wGoctadXGforestS6c3pGT20Nums, 2048),
    (wGoctadXGforestS6c3pGT21Labs, wGoctadXGforestS6c3pGT21Nums, 2048),
    (wGoctadXGforestS6c3pGT22Labs, wGoctadXGforestS6c3pGT22Nums, 1026)] 503488 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGoctadXGforestS6c3p_hn : wGoctadXGforestS6c3pL.sden * (octSumZ 64 true
    wGoctadXGforestS6c3pL wGoctadXGforestS6c3pW : ℚ) / 8 =
    wGoctadXGforestS6c3pW.sden * (selfOctP wGoctadXGforestS6c3pW : ℚ) := by
  rw [wGoctadXGforestS6c3p_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGoctadXGforestS6c3pW
      _ 503488 wGoctadXGforestS6c3p_Wsh wGoctadXGforestS6c3p_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
