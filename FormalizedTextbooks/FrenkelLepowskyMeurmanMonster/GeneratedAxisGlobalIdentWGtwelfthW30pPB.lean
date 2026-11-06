/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGtwelfthW30pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (octads) of the identification Twelfth[30]- <-> Twelfth[30]+ (record
gtwelfth:W30+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGtwelfthW30p_chk : OctadDense.octSumChk 64 5 true [(wGtwelfthW30pHT0Labs,
    wGtwelfthW30pHT0Nums, 2048), (wGtwelfthW30pHT1Labs, wGtwelfthW30pHT1Nums, 2048),
    (wGtwelfthW30pHT2Labs, wGtwelfthW30pHT2Nums, 2048), (wGtwelfthW30pHT3Labs,
    wGtwelfthW30pHT3Nums, 2048), (wGtwelfthW30pHT4Labs, wGtwelfthW30pHT4Nums, 2048),
    (wGtwelfthW30pHT5Labs, wGtwelfthW30pHT5Nums, 2048), (wGtwelfthW30pHT6Labs,
    wGtwelfthW30pHT6Nums, 2048), (wGtwelfthW30pHT7Labs, wGtwelfthW30pHT7Nums, 2048),
    (wGtwelfthW30pHT8Labs, wGtwelfthW30pHT8Nums, 2048), (wGtwelfthW30pHT9Labs,
    wGtwelfthW30pHT9Nums, 2048), (wGtwelfthW30pHT10Labs, wGtwelfthW30pHT10Nums, 2048),
    (wGtwelfthW30pHT11Labs, wGtwelfthW30pHT11Nums, 2048), (wGtwelfthW30pHT12Labs,
    wGtwelfthW30pHT12Nums, 2048), (wGtwelfthW30pHT13Labs, wGtwelfthW30pHT13Nums, 2048),
    (wGtwelfthW30pHT14Labs, wGtwelfthW30pHT14Nums, 2048), (wGtwelfthW30pHT15Labs,
    wGtwelfthW30pHT15Nums, 2048), (wGtwelfthW30pHT16Labs, wGtwelfthW30pHT16Nums, 2048),
    (wGtwelfthW30pHT17Labs, wGtwelfthW30pHT17Nums, 2048), (wGtwelfthW30pHT18Labs,
    wGtwelfthW30pHT18Nums, 2048), (wGtwelfthW30pHT19Labs, wGtwelfthW30pHT19Nums, 2048),
    (wGtwelfthW30pHT20Labs, wGtwelfthW30pHT20Nums, 2048), (wGtwelfthW30pHT21Labs,
    wGtwelfthW30pHT21Nums, 2048), (wGtwelfthW30pHT22Labs, wGtwelfthW30pHT22Nums, 1704)]
    [(wGtwelfthW30pGT0Labs, wGtwelfthW30pGT0Nums, 2048), (wGtwelfthW30pGT1Labs,
    wGtwelfthW30pGT1Nums, 2048), (wGtwelfthW30pGT2Labs, wGtwelfthW30pGT2Nums, 2048),
    (wGtwelfthW30pGT3Labs, wGtwelfthW30pGT3Nums, 2048), (wGtwelfthW30pGT4Labs,
    wGtwelfthW30pGT4Nums, 2048), (wGtwelfthW30pGT5Labs, wGtwelfthW30pGT5Nums, 2048),
    (wGtwelfthW30pGT6Labs, wGtwelfthW30pGT6Nums, 2048), (wGtwelfthW30pGT7Labs,
    wGtwelfthW30pGT7Nums, 2048), (wGtwelfthW30pGT8Labs, wGtwelfthW30pGT8Nums, 2048),
    (wGtwelfthW30pGT9Labs, wGtwelfthW30pGT9Nums, 2048), (wGtwelfthW30pGT10Labs,
    wGtwelfthW30pGT10Nums, 2048), (wGtwelfthW30pGT11Labs, wGtwelfthW30pGT11Nums, 2048),
    (wGtwelfthW30pGT12Labs, wGtwelfthW30pGT12Nums, 2048), (wGtwelfthW30pGT13Labs,
    wGtwelfthW30pGT13Nums, 2048), (wGtwelfthW30pGT14Labs, wGtwelfthW30pGT14Nums, 2048),
    (wGtwelfthW30pGT15Labs, wGtwelfthW30pGT15Nums, 2048), (wGtwelfthW30pGT16Labs,
    wGtwelfthW30pGT16Nums, 2048), (wGtwelfthW30pGT17Labs, wGtwelfthW30pGT17Nums, 2048),
    (wGtwelfthW30pGT18Labs, wGtwelfthW30pGT18Nums, 2048), (wGtwelfthW30pGT19Labs,
    wGtwelfthW30pGT19Nums, 2048), (wGtwelfthW30pGT20Labs, wGtwelfthW30pGT20Nums, 2048),
    (wGtwelfthW30pGT21Labs, wGtwelfthW30pGT21Nums, 2048), (wGtwelfthW30pGT22Labs,
    wGtwelfthW30pGT22Nums, 1704)] 4077568 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGtwelfthW30p_Lsh : wGtwelfthW30pL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGtwelfthW30pHT0Labs, wGtwelfthW30pHT0Nums, 2048), (wGtwelfthW30pHT1Labs,
    wGtwelfthW30pHT1Nums, 2048), (wGtwelfthW30pHT2Labs, wGtwelfthW30pHT2Nums, 2048),
    (wGtwelfthW30pHT3Labs, wGtwelfthW30pHT3Nums, 2048), (wGtwelfthW30pHT4Labs,
    wGtwelfthW30pHT4Nums, 2048), (wGtwelfthW30pHT5Labs, wGtwelfthW30pHT5Nums, 2048),
    (wGtwelfthW30pHT6Labs, wGtwelfthW30pHT6Nums, 2048), (wGtwelfthW30pHT7Labs,
    wGtwelfthW30pHT7Nums, 2048), (wGtwelfthW30pHT8Labs, wGtwelfthW30pHT8Nums, 2048),
    (wGtwelfthW30pHT9Labs, wGtwelfthW30pHT9Nums, 2048), (wGtwelfthW30pHT10Labs,
    wGtwelfthW30pHT10Nums, 2048), (wGtwelfthW30pHT11Labs, wGtwelfthW30pHT11Nums, 2048),
    (wGtwelfthW30pHT12Labs, wGtwelfthW30pHT12Nums, 2048), (wGtwelfthW30pHT13Labs,
    wGtwelfthW30pHT13Nums, 2048), (wGtwelfthW30pHT14Labs, wGtwelfthW30pHT14Nums, 2048),
    (wGtwelfthW30pHT15Labs, wGtwelfthW30pHT15Nums, 2048), (wGtwelfthW30pHT16Labs,
    wGtwelfthW30pHT16Nums, 2048), (wGtwelfthW30pHT17Labs, wGtwelfthW30pHT17Nums, 2048),
    (wGtwelfthW30pHT18Labs, wGtwelfthW30pHT18Nums, 2048), (wGtwelfthW30pHT19Labs,
    wGtwelfthW30pHT19Nums, 2048), (wGtwelfthW30pHT20Labs, wGtwelfthW30pHT20Nums, 2048),
    (wGtwelfthW30pHT21Labs, wGtwelfthW30pHT21Nums, 2048), (wGtwelfthW30pHT22Labs,
    wGtwelfthW30pHT22Nums, 1704)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGtwelfthW30p_Wsh : wGtwelfthW30pW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGtwelfthW30pGT0Labs, wGtwelfthW30pGT0Nums, 2048), (wGtwelfthW30pGT1Labs,
    wGtwelfthW30pGT1Nums, 2048), (wGtwelfthW30pGT2Labs, wGtwelfthW30pGT2Nums, 2048),
    (wGtwelfthW30pGT3Labs, wGtwelfthW30pGT3Nums, 2048), (wGtwelfthW30pGT4Labs,
    wGtwelfthW30pGT4Nums, 2048), (wGtwelfthW30pGT5Labs, wGtwelfthW30pGT5Nums, 2048),
    (wGtwelfthW30pGT6Labs, wGtwelfthW30pGT6Nums, 2048), (wGtwelfthW30pGT7Labs,
    wGtwelfthW30pGT7Nums, 2048), (wGtwelfthW30pGT8Labs, wGtwelfthW30pGT8Nums, 2048),
    (wGtwelfthW30pGT9Labs, wGtwelfthW30pGT9Nums, 2048), (wGtwelfthW30pGT10Labs,
    wGtwelfthW30pGT10Nums, 2048), (wGtwelfthW30pGT11Labs, wGtwelfthW30pGT11Nums, 2048),
    (wGtwelfthW30pGT12Labs, wGtwelfthW30pGT12Nums, 2048), (wGtwelfthW30pGT13Labs,
    wGtwelfthW30pGT13Nums, 2048), (wGtwelfthW30pGT14Labs, wGtwelfthW30pGT14Nums, 2048),
    (wGtwelfthW30pGT15Labs, wGtwelfthW30pGT15Nums, 2048), (wGtwelfthW30pGT16Labs,
    wGtwelfthW30pGT16Nums, 2048), (wGtwelfthW30pGT17Labs, wGtwelfthW30pGT17Nums, 2048),
    (wGtwelfthW30pGT18Labs, wGtwelfthW30pGT18Nums, 2048), (wGtwelfthW30pGT19Labs,
    wGtwelfthW30pGT19Nums, 2048), (wGtwelfthW30pGT20Labs, wGtwelfthW30pGT20Nums, 2048),
    (wGtwelfthW30pGT21Labs, wGtwelfthW30pGT21Nums, 2048), (wGtwelfthW30pGT22Labs,
    wGtwelfthW30pGT22Nums, 1704)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGtwelfthW30p_hok : octPackOk 64 wGtwelfthW30pL = true :=
  OctadDense.octPackOk_of_chk 64 5 true wGtwelfthW30pL _ _ 4077568 wGtwelfthW30p_Lsh
      wGtwelfthW30p_chk

/-- The octad integer sum. -/
theorem wGtwelfthW30p_octn : octSumZ 64 true wGtwelfthW30pL wGtwelfthW30pW = 4077568 :=
  OctadDense.octSumZ_of_chk 64 5 true wGtwelfthW30pL wGtwelfthW30pW _ _ 4077568 wGtwelfthW30p_Lsh
      wGtwelfthW30p_Wsh wGtwelfthW30p_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGtwelfthW30p_selfchk : OctadDense.selfOctChk 64 [(wGtwelfthW30pGT0Labs,
    wGtwelfthW30pGT0Nums, 2048), (wGtwelfthW30pGT1Labs, wGtwelfthW30pGT1Nums, 2048),
    (wGtwelfthW30pGT2Labs, wGtwelfthW30pGT2Nums, 2048), (wGtwelfthW30pGT3Labs,
    wGtwelfthW30pGT3Nums, 2048), (wGtwelfthW30pGT4Labs, wGtwelfthW30pGT4Nums, 2048),
    (wGtwelfthW30pGT5Labs, wGtwelfthW30pGT5Nums, 2048), (wGtwelfthW30pGT6Labs,
    wGtwelfthW30pGT6Nums, 2048), (wGtwelfthW30pGT7Labs, wGtwelfthW30pGT7Nums, 2048),
    (wGtwelfthW30pGT8Labs, wGtwelfthW30pGT8Nums, 2048), (wGtwelfthW30pGT9Labs,
    wGtwelfthW30pGT9Nums, 2048), (wGtwelfthW30pGT10Labs, wGtwelfthW30pGT10Nums, 2048),
    (wGtwelfthW30pGT11Labs, wGtwelfthW30pGT11Nums, 2048), (wGtwelfthW30pGT12Labs,
    wGtwelfthW30pGT12Nums, 2048), (wGtwelfthW30pGT13Labs, wGtwelfthW30pGT13Nums, 2048),
    (wGtwelfthW30pGT14Labs, wGtwelfthW30pGT14Nums, 2048), (wGtwelfthW30pGT15Labs,
    wGtwelfthW30pGT15Nums, 2048), (wGtwelfthW30pGT16Labs, wGtwelfthW30pGT16Nums, 2048),
    (wGtwelfthW30pGT17Labs, wGtwelfthW30pGT17Nums, 2048), (wGtwelfthW30pGT18Labs,
    wGtwelfthW30pGT18Nums, 2048), (wGtwelfthW30pGT19Labs, wGtwelfthW30pGT19Nums, 2048),
    (wGtwelfthW30pGT20Labs, wGtwelfthW30pGT20Nums, 2048), (wGtwelfthW30pGT21Labs,
    wGtwelfthW30pGT21Nums, 2048), (wGtwelfthW30pGT22Labs, wGtwelfthW30pGT22Nums, 1704)] 509696 =
    true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGtwelfthW30p_hn : wGtwelfthW30pL.sden * (octSumZ 64 true wGtwelfthW30pL wGtwelfthW30pW :
    ℚ) / 8 =
    wGtwelfthW30pW.sden * (selfOctP wGtwelfthW30pW : ℚ) := by
  rw [wGtwelfthW30p_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGtwelfthW30pW _ 509696
      wGtwelfthW30p_Wsh wGtwelfthW30p_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
