/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE33T32pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octads) of the identification Eighth[46]+ <-> Tenth[46]+ (record
goctad:E33@T32+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGoctadE33T32p_chk : OctadDense.octSumChk 64 6 true [(wGoctadE33T32pHT0Labs,
    wGoctadE33T32pHT0Nums, 2048), (wGoctadE33T32pHT1Labs, wGoctadE33T32pHT1Nums, 2048),
    (wGoctadE33T32pHT2Labs, wGoctadE33T32pHT2Nums, 2048), (wGoctadE33T32pHT3Labs,
    wGoctadE33T32pHT3Nums, 2048), (wGoctadE33T32pHT4Labs, wGoctadE33T32pHT4Nums, 2048),
    (wGoctadE33T32pHT5Labs, wGoctadE33T32pHT5Nums, 2048), (wGoctadE33T32pHT6Labs,
    wGoctadE33T32pHT6Nums, 2048), (wGoctadE33T32pHT7Labs, wGoctadE33T32pHT7Nums, 2048),
    (wGoctadE33T32pHT8Labs, wGoctadE33T32pHT8Nums, 2048), (wGoctadE33T32pHT9Labs,
    wGoctadE33T32pHT9Nums, 2048), (wGoctadE33T32pHT10Labs, wGoctadE33T32pHT10Nums, 2048),
    (wGoctadE33T32pHT11Labs, wGoctadE33T32pHT11Nums, 2048), (wGoctadE33T32pHT12Labs,
    wGoctadE33T32pHT12Nums, 2048), (wGoctadE33T32pHT13Labs, wGoctadE33T32pHT13Nums, 2048),
    (wGoctadE33T32pHT14Labs, wGoctadE33T32pHT14Nums, 2048), (wGoctadE33T32pHT15Labs,
    wGoctadE33T32pHT15Nums, 2048), (wGoctadE33T32pHT16Labs, wGoctadE33T32pHT16Nums, 2048),
    (wGoctadE33T32pHT17Labs, wGoctadE33T32pHT17Nums, 2048), (wGoctadE33T32pHT18Labs,
    wGoctadE33T32pHT18Nums, 2048), (wGoctadE33T32pHT19Labs, wGoctadE33T32pHT19Nums, 2048),
    (wGoctadE33T32pHT20Labs, wGoctadE33T32pHT20Nums, 2048), (wGoctadE33T32pHT21Labs,
    wGoctadE33T32pHT21Nums, 668)] [(wGoctadE33T32pGT0Labs, wGoctadE33T32pGT0Nums, 2048),
    (wGoctadE33T32pGT1Labs, wGoctadE33T32pGT1Nums, 2048), (wGoctadE33T32pGT2Labs,
    wGoctadE33T32pGT2Nums, 2048), (wGoctadE33T32pGT3Labs, wGoctadE33T32pGT3Nums, 2048),
    (wGoctadE33T32pGT4Labs, wGoctadE33T32pGT4Nums, 2048), (wGoctadE33T32pGT5Labs,
    wGoctadE33T32pGT5Nums, 2048), (wGoctadE33T32pGT6Labs, wGoctadE33T32pGT6Nums, 2048),
    (wGoctadE33T32pGT7Labs, wGoctadE33T32pGT7Nums, 2048), (wGoctadE33T32pGT8Labs,
    wGoctadE33T32pGT8Nums, 2048), (wGoctadE33T32pGT9Labs, wGoctadE33T32pGT9Nums, 2048),
    (wGoctadE33T32pGT10Labs, wGoctadE33T32pGT10Nums, 2048), (wGoctadE33T32pGT11Labs,
    wGoctadE33T32pGT11Nums, 2048), (wGoctadE33T32pGT12Labs, wGoctadE33T32pGT12Nums, 2048),
    (wGoctadE33T32pGT13Labs, wGoctadE33T32pGT13Nums, 2048), (wGoctadE33T32pGT14Labs,
    wGoctadE33T32pGT14Nums, 2048), (wGoctadE33T32pGT15Labs, wGoctadE33T32pGT15Nums, 2048),
    (wGoctadE33T32pGT16Labs, wGoctadE33T32pGT16Nums, 2048), (wGoctadE33T32pGT17Labs,
    wGoctadE33T32pGT17Nums, 2048), (wGoctadE33T32pGT18Labs, wGoctadE33T32pGT18Nums, 2048),
    (wGoctadE33T32pGT19Labs, wGoctadE33T32pGT19Nums, 2048), (wGoctadE33T32pGT20Labs,
    wGoctadE33T32pGT20Nums, 2048), (wGoctadE33T32pGT21Labs, wGoctadE33T32pGT21Nums, 2048),
    (wGoctadE33T32pGT22Labs, wGoctadE33T32pGT22Nums, 1026)] 1015552 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGoctadE33T32p_Lsh : wGoctadE33T32pL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGoctadE33T32pHT0Labs, wGoctadE33T32pHT0Nums, 2048), (wGoctadE33T32pHT1Labs,
    wGoctadE33T32pHT1Nums, 2048), (wGoctadE33T32pHT2Labs, wGoctadE33T32pHT2Nums, 2048),
    (wGoctadE33T32pHT3Labs, wGoctadE33T32pHT3Nums, 2048), (wGoctadE33T32pHT4Labs,
    wGoctadE33T32pHT4Nums, 2048), (wGoctadE33T32pHT5Labs, wGoctadE33T32pHT5Nums, 2048),
    (wGoctadE33T32pHT6Labs, wGoctadE33T32pHT6Nums, 2048), (wGoctadE33T32pHT7Labs,
    wGoctadE33T32pHT7Nums, 2048), (wGoctadE33T32pHT8Labs, wGoctadE33T32pHT8Nums, 2048),
    (wGoctadE33T32pHT9Labs, wGoctadE33T32pHT9Nums, 2048), (wGoctadE33T32pHT10Labs,
    wGoctadE33T32pHT10Nums, 2048), (wGoctadE33T32pHT11Labs, wGoctadE33T32pHT11Nums, 2048),
    (wGoctadE33T32pHT12Labs, wGoctadE33T32pHT12Nums, 2048), (wGoctadE33T32pHT13Labs,
    wGoctadE33T32pHT13Nums, 2048), (wGoctadE33T32pHT14Labs, wGoctadE33T32pHT14Nums, 2048),
    (wGoctadE33T32pHT15Labs, wGoctadE33T32pHT15Nums, 2048), (wGoctadE33T32pHT16Labs,
    wGoctadE33T32pHT16Nums, 2048), (wGoctadE33T32pHT17Labs, wGoctadE33T32pHT17Nums, 2048),
    (wGoctadE33T32pHT18Labs, wGoctadE33T32pHT18Nums, 2048), (wGoctadE33T32pHT19Labs,
    wGoctadE33T32pHT19Nums, 2048), (wGoctadE33T32pHT20Labs, wGoctadE33T32pHT20Nums, 2048),
    (wGoctadE33T32pHT21Labs, wGoctadE33T32pHT21Nums, 668)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGoctadE33T32p_Wsh : wGoctadE33T32pW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGoctadE33T32pGT0Labs, wGoctadE33T32pGT0Nums, 2048), (wGoctadE33T32pGT1Labs,
    wGoctadE33T32pGT1Nums, 2048), (wGoctadE33T32pGT2Labs, wGoctadE33T32pGT2Nums, 2048),
    (wGoctadE33T32pGT3Labs, wGoctadE33T32pGT3Nums, 2048), (wGoctadE33T32pGT4Labs,
    wGoctadE33T32pGT4Nums, 2048), (wGoctadE33T32pGT5Labs, wGoctadE33T32pGT5Nums, 2048),
    (wGoctadE33T32pGT6Labs, wGoctadE33T32pGT6Nums, 2048), (wGoctadE33T32pGT7Labs,
    wGoctadE33T32pGT7Nums, 2048), (wGoctadE33T32pGT8Labs, wGoctadE33T32pGT8Nums, 2048),
    (wGoctadE33T32pGT9Labs, wGoctadE33T32pGT9Nums, 2048), (wGoctadE33T32pGT10Labs,
    wGoctadE33T32pGT10Nums, 2048), (wGoctadE33T32pGT11Labs, wGoctadE33T32pGT11Nums, 2048),
    (wGoctadE33T32pGT12Labs, wGoctadE33T32pGT12Nums, 2048), (wGoctadE33T32pGT13Labs,
    wGoctadE33T32pGT13Nums, 2048), (wGoctadE33T32pGT14Labs, wGoctadE33T32pGT14Nums, 2048),
    (wGoctadE33T32pGT15Labs, wGoctadE33T32pGT15Nums, 2048), (wGoctadE33T32pGT16Labs,
    wGoctadE33T32pGT16Nums, 2048), (wGoctadE33T32pGT17Labs, wGoctadE33T32pGT17Nums, 2048),
    (wGoctadE33T32pGT18Labs, wGoctadE33T32pGT18Nums, 2048), (wGoctadE33T32pGT19Labs,
    wGoctadE33T32pGT19Nums, 2048), (wGoctadE33T32pGT20Labs, wGoctadE33T32pGT20Nums, 2048),
    (wGoctadE33T32pGT21Labs, wGoctadE33T32pGT21Nums, 2048), (wGoctadE33T32pGT22Labs,
    wGoctadE33T32pGT22Nums, 1026)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGoctadE33T32p_hok : octPackOk 64 wGoctadE33T32pL = true :=
  OctadDense.octPackOk_of_chk 64 6 true wGoctadE33T32pL _ _ 1015552 wGoctadE33T32p_Lsh
      wGoctadE33T32p_chk

/-- The octad integer sum. -/
theorem wGoctadE33T32p_octn : octSumZ 64 true wGoctadE33T32pL wGoctadE33T32pW = 1015552 :=
  OctadDense.octSumZ_of_chk 64 6 true wGoctadE33T32pL wGoctadE33T32pW _ _ 1015552
      wGoctadE33T32p_Lsh wGoctadE33T32p_Wsh wGoctadE33T32p_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGoctadE33T32p_selfchk : OctadDense.selfOctChk 64 [(wGoctadE33T32pGT0Labs,
    wGoctadE33T32pGT0Nums, 2048), (wGoctadE33T32pGT1Labs, wGoctadE33T32pGT1Nums, 2048),
    (wGoctadE33T32pGT2Labs, wGoctadE33T32pGT2Nums, 2048), (wGoctadE33T32pGT3Labs,
    wGoctadE33T32pGT3Nums, 2048), (wGoctadE33T32pGT4Labs, wGoctadE33T32pGT4Nums, 2048),
    (wGoctadE33T32pGT5Labs, wGoctadE33T32pGT5Nums, 2048), (wGoctadE33T32pGT6Labs,
    wGoctadE33T32pGT6Nums, 2048), (wGoctadE33T32pGT7Labs, wGoctadE33T32pGT7Nums, 2048),
    (wGoctadE33T32pGT8Labs, wGoctadE33T32pGT8Nums, 2048), (wGoctadE33T32pGT9Labs,
    wGoctadE33T32pGT9Nums, 2048), (wGoctadE33T32pGT10Labs, wGoctadE33T32pGT10Nums, 2048),
    (wGoctadE33T32pGT11Labs, wGoctadE33T32pGT11Nums, 2048), (wGoctadE33T32pGT12Labs,
    wGoctadE33T32pGT12Nums, 2048), (wGoctadE33T32pGT13Labs, wGoctadE33T32pGT13Nums, 2048),
    (wGoctadE33T32pGT14Labs, wGoctadE33T32pGT14Nums, 2048), (wGoctadE33T32pGT15Labs,
    wGoctadE33T32pGT15Nums, 2048), (wGoctadE33T32pGT16Labs, wGoctadE33T32pGT16Nums, 2048),
    (wGoctadE33T32pGT17Labs, wGoctadE33T32pGT17Nums, 2048), (wGoctadE33T32pGT18Labs,
    wGoctadE33T32pGT18Nums, 2048), (wGoctadE33T32pGT19Labs, wGoctadE33T32pGT19Nums, 2048),
    (wGoctadE33T32pGT20Labs, wGoctadE33T32pGT20Nums, 2048), (wGoctadE33T32pGT21Labs,
    wGoctadE33T32pGT21Nums, 2048), (wGoctadE33T32pGT22Labs, wGoctadE33T32pGT22Nums, 1026)] 507776
    = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGoctadE33T32p_hn : wGoctadE33T32pL.sden * (octSumZ 64 true wGoctadE33T32pL
    wGoctadE33T32pW : ℚ) / 8 =
    wGoctadE33T32pW.sden * (selfOctP wGoctadE33T32pW : ℚ) := by
  rw [wGoctadE33T32p_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGoctadE33T32pW _ 507776
      wGoctadE33T32p_Wsh wGoctadE33T32p_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
