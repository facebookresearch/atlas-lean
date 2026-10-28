/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE19T33pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octads) of the identification Eighth[24]+ <-> Tenth[61]+ (record
goctad:E19@T33+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGoctadE19T33p_chk : OctadDense.octSumChk 64 7 true [(wGoctadE19T33pHT0Labs,
    wGoctadE19T33pHT0Nums, 2048), (wGoctadE19T33pHT1Labs, wGoctadE19T33pHT1Nums, 2048),
    (wGoctadE19T33pHT2Labs, wGoctadE19T33pHT2Nums, 2048), (wGoctadE19T33pHT3Labs,
    wGoctadE19T33pHT3Nums, 2048), (wGoctadE19T33pHT4Labs, wGoctadE19T33pHT4Nums, 2048),
    (wGoctadE19T33pHT5Labs, wGoctadE19T33pHT5Nums, 2048), (wGoctadE19T33pHT6Labs,
    wGoctadE19T33pHT6Nums, 2048), (wGoctadE19T33pHT7Labs, wGoctadE19T33pHT7Nums, 2048),
    (wGoctadE19T33pHT8Labs, wGoctadE19T33pHT8Nums, 2048), (wGoctadE19T33pHT9Labs,
    wGoctadE19T33pHT9Nums, 2048), (wGoctadE19T33pHT10Labs, wGoctadE19T33pHT10Nums, 2048),
    (wGoctadE19T33pHT11Labs, wGoctadE19T33pHT11Nums, 2048), (wGoctadE19T33pHT12Labs,
    wGoctadE19T33pHT12Nums, 2048), (wGoctadE19T33pHT13Labs, wGoctadE19T33pHT13Nums, 2048),
    (wGoctadE19T33pHT14Labs, wGoctadE19T33pHT14Nums, 2048), (wGoctadE19T33pHT15Labs,
    wGoctadE19T33pHT15Nums, 2048), (wGoctadE19T33pHT16Labs, wGoctadE19T33pHT16Nums, 2048),
    (wGoctadE19T33pHT17Labs, wGoctadE19T33pHT17Nums, 2048), (wGoctadE19T33pHT18Labs,
    wGoctadE19T33pHT18Nums, 2048), (wGoctadE19T33pHT19Labs, wGoctadE19T33pHT19Nums, 2048),
    (wGoctadE19T33pHT20Labs, wGoctadE19T33pHT20Nums, 2048), (wGoctadE19T33pHT21Labs,
    wGoctadE19T33pHT21Nums, 668)] [(wGoctadE19T33pGT0Labs, wGoctadE19T33pGT0Nums, 2048),
    (wGoctadE19T33pGT1Labs, wGoctadE19T33pGT1Nums, 2048), (wGoctadE19T33pGT2Labs,
    wGoctadE19T33pGT2Nums, 2048), (wGoctadE19T33pGT3Labs, wGoctadE19T33pGT3Nums, 2048),
    (wGoctadE19T33pGT4Labs, wGoctadE19T33pGT4Nums, 2048), (wGoctadE19T33pGT5Labs,
    wGoctadE19T33pGT5Nums, 2048), (wGoctadE19T33pGT6Labs, wGoctadE19T33pGT6Nums, 2048),
    (wGoctadE19T33pGT7Labs, wGoctadE19T33pGT7Nums, 2048), (wGoctadE19T33pGT8Labs,
    wGoctadE19T33pGT8Nums, 2048), (wGoctadE19T33pGT9Labs, wGoctadE19T33pGT9Nums, 2048),
    (wGoctadE19T33pGT10Labs, wGoctadE19T33pGT10Nums, 2048), (wGoctadE19T33pGT11Labs,
    wGoctadE19T33pGT11Nums, 2048), (wGoctadE19T33pGT12Labs, wGoctadE19T33pGT12Nums, 2048),
    (wGoctadE19T33pGT13Labs, wGoctadE19T33pGT13Nums, 2048), (wGoctadE19T33pGT14Labs,
    wGoctadE19T33pGT14Nums, 2048), (wGoctadE19T33pGT15Labs, wGoctadE19T33pGT15Nums, 2048),
    (wGoctadE19T33pGT16Labs, wGoctadE19T33pGT16Nums, 2048), (wGoctadE19T33pGT17Labs,
    wGoctadE19T33pGT17Nums, 2048), (wGoctadE19T33pGT18Labs, wGoctadE19T33pGT18Nums, 2048),
    (wGoctadE19T33pGT19Labs, wGoctadE19T33pGT19Nums, 2048), (wGoctadE19T33pGT20Labs,
    wGoctadE19T33pGT20Nums, 2048), (wGoctadE19T33pGT21Labs, wGoctadE19T33pGT21Nums, 2048),
    (wGoctadE19T33pGT22Labs, wGoctadE19T33pGT22Nums, 1026)] 1015808 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGoctadE19T33p_Lsh : wGoctadE19T33pL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGoctadE19T33pHT0Labs, wGoctadE19T33pHT0Nums, 2048), (wGoctadE19T33pHT1Labs,
    wGoctadE19T33pHT1Nums, 2048), (wGoctadE19T33pHT2Labs, wGoctadE19T33pHT2Nums, 2048),
    (wGoctadE19T33pHT3Labs, wGoctadE19T33pHT3Nums, 2048), (wGoctadE19T33pHT4Labs,
    wGoctadE19T33pHT4Nums, 2048), (wGoctadE19T33pHT5Labs, wGoctadE19T33pHT5Nums, 2048),
    (wGoctadE19T33pHT6Labs, wGoctadE19T33pHT6Nums, 2048), (wGoctadE19T33pHT7Labs,
    wGoctadE19T33pHT7Nums, 2048), (wGoctadE19T33pHT8Labs, wGoctadE19T33pHT8Nums, 2048),
    (wGoctadE19T33pHT9Labs, wGoctadE19T33pHT9Nums, 2048), (wGoctadE19T33pHT10Labs,
    wGoctadE19T33pHT10Nums, 2048), (wGoctadE19T33pHT11Labs, wGoctadE19T33pHT11Nums, 2048),
    (wGoctadE19T33pHT12Labs, wGoctadE19T33pHT12Nums, 2048), (wGoctadE19T33pHT13Labs,
    wGoctadE19T33pHT13Nums, 2048), (wGoctadE19T33pHT14Labs, wGoctadE19T33pHT14Nums, 2048),
    (wGoctadE19T33pHT15Labs, wGoctadE19T33pHT15Nums, 2048), (wGoctadE19T33pHT16Labs,
    wGoctadE19T33pHT16Nums, 2048), (wGoctadE19T33pHT17Labs, wGoctadE19T33pHT17Nums, 2048),
    (wGoctadE19T33pHT18Labs, wGoctadE19T33pHT18Nums, 2048), (wGoctadE19T33pHT19Labs,
    wGoctadE19T33pHT19Nums, 2048), (wGoctadE19T33pHT20Labs, wGoctadE19T33pHT20Nums, 2048),
    (wGoctadE19T33pHT21Labs, wGoctadE19T33pHT21Nums, 668)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGoctadE19T33p_Wsh : wGoctadE19T33pW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGoctadE19T33pGT0Labs, wGoctadE19T33pGT0Nums, 2048), (wGoctadE19T33pGT1Labs,
    wGoctadE19T33pGT1Nums, 2048), (wGoctadE19T33pGT2Labs, wGoctadE19T33pGT2Nums, 2048),
    (wGoctadE19T33pGT3Labs, wGoctadE19T33pGT3Nums, 2048), (wGoctadE19T33pGT4Labs,
    wGoctadE19T33pGT4Nums, 2048), (wGoctadE19T33pGT5Labs, wGoctadE19T33pGT5Nums, 2048),
    (wGoctadE19T33pGT6Labs, wGoctadE19T33pGT6Nums, 2048), (wGoctadE19T33pGT7Labs,
    wGoctadE19T33pGT7Nums, 2048), (wGoctadE19T33pGT8Labs, wGoctadE19T33pGT8Nums, 2048),
    (wGoctadE19T33pGT9Labs, wGoctadE19T33pGT9Nums, 2048), (wGoctadE19T33pGT10Labs,
    wGoctadE19T33pGT10Nums, 2048), (wGoctadE19T33pGT11Labs, wGoctadE19T33pGT11Nums, 2048),
    (wGoctadE19T33pGT12Labs, wGoctadE19T33pGT12Nums, 2048), (wGoctadE19T33pGT13Labs,
    wGoctadE19T33pGT13Nums, 2048), (wGoctadE19T33pGT14Labs, wGoctadE19T33pGT14Nums, 2048),
    (wGoctadE19T33pGT15Labs, wGoctadE19T33pGT15Nums, 2048), (wGoctadE19T33pGT16Labs,
    wGoctadE19T33pGT16Nums, 2048), (wGoctadE19T33pGT17Labs, wGoctadE19T33pGT17Nums, 2048),
    (wGoctadE19T33pGT18Labs, wGoctadE19T33pGT18Nums, 2048), (wGoctadE19T33pGT19Labs,
    wGoctadE19T33pGT19Nums, 2048), (wGoctadE19T33pGT20Labs, wGoctadE19T33pGT20Nums, 2048),
    (wGoctadE19T33pGT21Labs, wGoctadE19T33pGT21Nums, 2048), (wGoctadE19T33pGT22Labs,
    wGoctadE19T33pGT22Nums, 1026)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGoctadE19T33p_hok : octPackOk 64 wGoctadE19T33pL = true :=
  OctadDense.octPackOk_of_chk 64 7 true wGoctadE19T33pL _ _ 1015808 wGoctadE19T33p_Lsh
      wGoctadE19T33p_chk

/-- The octad integer sum. -/
theorem wGoctadE19T33p_octn : octSumZ 64 true wGoctadE19T33pL wGoctadE19T33pW = 1015808 :=
  OctadDense.octSumZ_of_chk 64 7 true wGoctadE19T33pL wGoctadE19T33pW _ _ 1015808
      wGoctadE19T33p_Lsh wGoctadE19T33p_Wsh wGoctadE19T33p_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGoctadE19T33p_selfchk : OctadDense.selfOctChk 64 [(wGoctadE19T33pGT0Labs,
    wGoctadE19T33pGT0Nums, 2048), (wGoctadE19T33pGT1Labs, wGoctadE19T33pGT1Nums, 2048),
    (wGoctadE19T33pGT2Labs, wGoctadE19T33pGT2Nums, 2048), (wGoctadE19T33pGT3Labs,
    wGoctadE19T33pGT3Nums, 2048), (wGoctadE19T33pGT4Labs, wGoctadE19T33pGT4Nums, 2048),
    (wGoctadE19T33pGT5Labs, wGoctadE19T33pGT5Nums, 2048), (wGoctadE19T33pGT6Labs,
    wGoctadE19T33pGT6Nums, 2048), (wGoctadE19T33pGT7Labs, wGoctadE19T33pGT7Nums, 2048),
    (wGoctadE19T33pGT8Labs, wGoctadE19T33pGT8Nums, 2048), (wGoctadE19T33pGT9Labs,
    wGoctadE19T33pGT9Nums, 2048), (wGoctadE19T33pGT10Labs, wGoctadE19T33pGT10Nums, 2048),
    (wGoctadE19T33pGT11Labs, wGoctadE19T33pGT11Nums, 2048), (wGoctadE19T33pGT12Labs,
    wGoctadE19T33pGT12Nums, 2048), (wGoctadE19T33pGT13Labs, wGoctadE19T33pGT13Nums, 2048),
    (wGoctadE19T33pGT14Labs, wGoctadE19T33pGT14Nums, 2048), (wGoctadE19T33pGT15Labs,
    wGoctadE19T33pGT15Nums, 2048), (wGoctadE19T33pGT16Labs, wGoctadE19T33pGT16Nums, 2048),
    (wGoctadE19T33pGT17Labs, wGoctadE19T33pGT17Nums, 2048), (wGoctadE19T33pGT18Labs,
    wGoctadE19T33pGT18Nums, 2048), (wGoctadE19T33pGT19Labs, wGoctadE19T33pGT19Nums, 2048),
    (wGoctadE19T33pGT20Labs, wGoctadE19T33pGT20Nums, 2048), (wGoctadE19T33pGT21Labs,
    wGoctadE19T33pGT21Nums, 2048), (wGoctadE19T33pGT22Labs, wGoctadE19T33pGT22Nums, 1026)] 507904
    = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGoctadE19T33p_hn : wGoctadE19T33pL.sden * (octSumZ 64 true wGoctadE19T33pL
    wGoctadE19T33pW : ℚ) / 8 =
    wGoctadE19T33pW.sden * (selfOctP wGoctadE19T33pW : ℚ) := by
  rw [wGoctadE19T33p_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGoctadE19T33pW _ 507904
      wGoctadE19T33p_Wsh wGoctadE19T33p_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
