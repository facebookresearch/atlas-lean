/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGoctadE18nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octads) of the identification Eighth[23]- <-> Tenth[58]- (record goctad:E18-,
e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGoctadXGoctadE18n_chk : OctadDense.octSumChk 64 6 false [(wGoctadXGoctadE18nHT0Labs,
    wGoctadXGoctadE18nHT0Nums, 2048), (wGoctadXGoctadE18nHT1Labs, wGoctadXGoctadE18nHT1Nums,
    2048), (wGoctadXGoctadE18nHT2Labs, wGoctadXGoctadE18nHT2Nums, 2048),
    (wGoctadXGoctadE18nHT3Labs, wGoctadXGoctadE18nHT3Nums, 2048), (wGoctadXGoctadE18nHT4Labs,
    wGoctadXGoctadE18nHT4Nums, 2048), (wGoctadXGoctadE18nHT5Labs, wGoctadXGoctadE18nHT5Nums,
    2048), (wGoctadXGoctadE18nHT6Labs, wGoctadXGoctadE18nHT6Nums, 2048),
    (wGoctadXGoctadE18nHT7Labs, wGoctadXGoctadE18nHT7Nums, 2048), (wGoctadXGoctadE18nHT8Labs,
    wGoctadXGoctadE18nHT8Nums, 2048), (wGoctadXGoctadE18nHT9Labs, wGoctadXGoctadE18nHT9Nums,
    2048), (wGoctadXGoctadE18nHT10Labs, wGoctadXGoctadE18nHT10Nums, 2048),
    (wGoctadXGoctadE18nHT11Labs, wGoctadXGoctadE18nHT11Nums, 2048), (wGoctadXGoctadE18nHT12Labs,
    wGoctadXGoctadE18nHT12Nums, 2048), (wGoctadXGoctadE18nHT13Labs, wGoctadXGoctadE18nHT13Nums,
    2048), (wGoctadXGoctadE18nHT14Labs, wGoctadXGoctadE18nHT14Nums, 2048),
    (wGoctadXGoctadE18nHT15Labs, wGoctadXGoctadE18nHT15Nums, 2048), (wGoctadXGoctadE18nHT16Labs,
    wGoctadXGoctadE18nHT16Nums, 2048), (wGoctadXGoctadE18nHT17Labs, wGoctadXGoctadE18nHT17Nums,
    2048), (wGoctadXGoctadE18nHT18Labs, wGoctadXGoctadE18nHT18Nums, 2048),
    (wGoctadXGoctadE18nHT19Labs, wGoctadXGoctadE18nHT19Nums, 2048), (wGoctadXGoctadE18nHT20Labs,
    wGoctadXGoctadE18nHT20Nums, 2048), (wGoctadXGoctadE18nHT21Labs, wGoctadXGoctadE18nHT21Nums,
    668)] [(wGoctadXGoctadE18nGT0Labs, wGoctadXGoctadE18nGT0Nums, 2048),
    (wGoctadXGoctadE18nGT1Labs, wGoctadXGoctadE18nGT1Nums, 2048), (wGoctadXGoctadE18nGT2Labs,
    wGoctadXGoctadE18nGT2Nums, 2048), (wGoctadXGoctadE18nGT3Labs, wGoctadXGoctadE18nGT3Nums,
    2048), (wGoctadXGoctadE18nGT4Labs, wGoctadXGoctadE18nGT4Nums, 2048),
    (wGoctadXGoctadE18nGT5Labs, wGoctadXGoctadE18nGT5Nums, 2048), (wGoctadXGoctadE18nGT6Labs,
    wGoctadXGoctadE18nGT6Nums, 2048), (wGoctadXGoctadE18nGT7Labs, wGoctadXGoctadE18nGT7Nums,
    2048), (wGoctadXGoctadE18nGT8Labs, wGoctadXGoctadE18nGT8Nums, 2048),
    (wGoctadXGoctadE18nGT9Labs, wGoctadXGoctadE18nGT9Nums, 2048), (wGoctadXGoctadE18nGT10Labs,
    wGoctadXGoctadE18nGT10Nums, 2048), (wGoctadXGoctadE18nGT11Labs, wGoctadXGoctadE18nGT11Nums,
    2048), (wGoctadXGoctadE18nGT12Labs, wGoctadXGoctadE18nGT12Nums, 2048),
    (wGoctadXGoctadE18nGT13Labs, wGoctadXGoctadE18nGT13Nums, 2048), (wGoctadXGoctadE18nGT14Labs,
    wGoctadXGoctadE18nGT14Nums, 2048), (wGoctadXGoctadE18nGT15Labs, wGoctadXGoctadE18nGT15Nums,
    2048), (wGoctadXGoctadE18nGT16Labs, wGoctadXGoctadE18nGT16Nums, 2048),
    (wGoctadXGoctadE18nGT17Labs, wGoctadXGoctadE18nGT17Nums, 2048), (wGoctadXGoctadE18nGT18Labs,
    wGoctadXGoctadE18nGT18Nums, 2048), (wGoctadXGoctadE18nGT19Labs, wGoctadXGoctadE18nGT19Nums,
    2048), (wGoctadXGoctadE18nGT20Labs, wGoctadXGoctadE18nGT20Nums, 2048),
    (wGoctadXGoctadE18nGT21Labs, wGoctadXGoctadE18nGT21Nums, 2048), (wGoctadXGoctadE18nGT22Labs,
    wGoctadXGoctadE18nGT22Nums, 1026)] 1024896 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGoctadXGoctadE18n_Lsh : wGoctadXGoctadE18nL.sh = ShortData.ofList
    (OctadDense.octChunkTerms [(wGoctadXGoctadE18nHT0Labs, wGoctadXGoctadE18nHT0Nums, 2048),
    (wGoctadXGoctadE18nHT1Labs, wGoctadXGoctadE18nHT1Nums, 2048), (wGoctadXGoctadE18nHT2Labs,
    wGoctadXGoctadE18nHT2Nums, 2048), (wGoctadXGoctadE18nHT3Labs, wGoctadXGoctadE18nHT3Nums,
    2048), (wGoctadXGoctadE18nHT4Labs, wGoctadXGoctadE18nHT4Nums, 2048),
    (wGoctadXGoctadE18nHT5Labs, wGoctadXGoctadE18nHT5Nums, 2048), (wGoctadXGoctadE18nHT6Labs,
    wGoctadXGoctadE18nHT6Nums, 2048), (wGoctadXGoctadE18nHT7Labs, wGoctadXGoctadE18nHT7Nums,
    2048), (wGoctadXGoctadE18nHT8Labs, wGoctadXGoctadE18nHT8Nums, 2048),
    (wGoctadXGoctadE18nHT9Labs, wGoctadXGoctadE18nHT9Nums, 2048), (wGoctadXGoctadE18nHT10Labs,
    wGoctadXGoctadE18nHT10Nums, 2048), (wGoctadXGoctadE18nHT11Labs, wGoctadXGoctadE18nHT11Nums,
    2048), (wGoctadXGoctadE18nHT12Labs, wGoctadXGoctadE18nHT12Nums, 2048),
    (wGoctadXGoctadE18nHT13Labs, wGoctadXGoctadE18nHT13Nums, 2048), (wGoctadXGoctadE18nHT14Labs,
    wGoctadXGoctadE18nHT14Nums, 2048), (wGoctadXGoctadE18nHT15Labs, wGoctadXGoctadE18nHT15Nums,
    2048), (wGoctadXGoctadE18nHT16Labs, wGoctadXGoctadE18nHT16Nums, 2048),
    (wGoctadXGoctadE18nHT17Labs, wGoctadXGoctadE18nHT17Nums, 2048), (wGoctadXGoctadE18nHT18Labs,
    wGoctadXGoctadE18nHT18Nums, 2048), (wGoctadXGoctadE18nHT19Labs, wGoctadXGoctadE18nHT19Nums,
    2048), (wGoctadXGoctadE18nHT20Labs, wGoctadXGoctadE18nHT20Nums, 2048),
    (wGoctadXGoctadE18nHT21Labs, wGoctadXGoctadE18nHT21Nums, 668)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGoctadXGoctadE18n_Wsh : wGoctadXGoctadE18nW.sh = ShortData.ofList
    (OctadDense.octChunkTerms [(wGoctadXGoctadE18nGT0Labs, wGoctadXGoctadE18nGT0Nums, 2048),
    (wGoctadXGoctadE18nGT1Labs, wGoctadXGoctadE18nGT1Nums, 2048), (wGoctadXGoctadE18nGT2Labs,
    wGoctadXGoctadE18nGT2Nums, 2048), (wGoctadXGoctadE18nGT3Labs, wGoctadXGoctadE18nGT3Nums,
    2048), (wGoctadXGoctadE18nGT4Labs, wGoctadXGoctadE18nGT4Nums, 2048),
    (wGoctadXGoctadE18nGT5Labs, wGoctadXGoctadE18nGT5Nums, 2048), (wGoctadXGoctadE18nGT6Labs,
    wGoctadXGoctadE18nGT6Nums, 2048), (wGoctadXGoctadE18nGT7Labs, wGoctadXGoctadE18nGT7Nums,
    2048), (wGoctadXGoctadE18nGT8Labs, wGoctadXGoctadE18nGT8Nums, 2048),
    (wGoctadXGoctadE18nGT9Labs, wGoctadXGoctadE18nGT9Nums, 2048), (wGoctadXGoctadE18nGT10Labs,
    wGoctadXGoctadE18nGT10Nums, 2048), (wGoctadXGoctadE18nGT11Labs, wGoctadXGoctadE18nGT11Nums,
    2048), (wGoctadXGoctadE18nGT12Labs, wGoctadXGoctadE18nGT12Nums, 2048),
    (wGoctadXGoctadE18nGT13Labs, wGoctadXGoctadE18nGT13Nums, 2048), (wGoctadXGoctadE18nGT14Labs,
    wGoctadXGoctadE18nGT14Nums, 2048), (wGoctadXGoctadE18nGT15Labs, wGoctadXGoctadE18nGT15Nums,
    2048), (wGoctadXGoctadE18nGT16Labs, wGoctadXGoctadE18nGT16Nums, 2048),
    (wGoctadXGoctadE18nGT17Labs, wGoctadXGoctadE18nGT17Nums, 2048), (wGoctadXGoctadE18nGT18Labs,
    wGoctadXGoctadE18nGT18Nums, 2048), (wGoctadXGoctadE18nGT19Labs, wGoctadXGoctadE18nGT19Nums,
    2048), (wGoctadXGoctadE18nGT20Labs, wGoctadXGoctadE18nGT20Nums, 2048),
    (wGoctadXGoctadE18nGT21Labs, wGoctadXGoctadE18nGT21Nums, 2048), (wGoctadXGoctadE18nGT22Labs,
    wGoctadXGoctadE18nGT22Nums, 1026)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGoctadXGoctadE18n_hok : octPackOk 64 wGoctadXGoctadE18nL = true :=
  OctadDense.octPackOk_of_chk 64 6 false wGoctadXGoctadE18nL _ _ 1024896 wGoctadXGoctadE18n_Lsh
      wGoctadXGoctadE18n_chk

/-- The octad integer sum. -/
theorem wGoctadXGoctadE18n_octn : octSumZ 64 false wGoctadXGoctadE18nL wGoctadXGoctadE18nW =
    1024896 :=
  OctadDense.octSumZ_of_chk 64 6 false wGoctadXGoctadE18nL wGoctadXGoctadE18nW _ _ 1024896
      wGoctadXGoctadE18n_Lsh wGoctadXGoctadE18n_Wsh wGoctadXGoctadE18n_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGoctadXGoctadE18n_selfchk : OctadDense.selfOctChk 64 [(wGoctadXGoctadE18nGT0Labs,
    wGoctadXGoctadE18nGT0Nums, 2048), (wGoctadXGoctadE18nGT1Labs, wGoctadXGoctadE18nGT1Nums,
    2048), (wGoctadXGoctadE18nGT2Labs, wGoctadXGoctadE18nGT2Nums, 2048),
    (wGoctadXGoctadE18nGT3Labs, wGoctadXGoctadE18nGT3Nums, 2048), (wGoctadXGoctadE18nGT4Labs,
    wGoctadXGoctadE18nGT4Nums, 2048), (wGoctadXGoctadE18nGT5Labs, wGoctadXGoctadE18nGT5Nums,
    2048), (wGoctadXGoctadE18nGT6Labs, wGoctadXGoctadE18nGT6Nums, 2048),
    (wGoctadXGoctadE18nGT7Labs, wGoctadXGoctadE18nGT7Nums, 2048), (wGoctadXGoctadE18nGT8Labs,
    wGoctadXGoctadE18nGT8Nums, 2048), (wGoctadXGoctadE18nGT9Labs, wGoctadXGoctadE18nGT9Nums,
    2048), (wGoctadXGoctadE18nGT10Labs, wGoctadXGoctadE18nGT10Nums, 2048),
    (wGoctadXGoctadE18nGT11Labs, wGoctadXGoctadE18nGT11Nums, 2048), (wGoctadXGoctadE18nGT12Labs,
    wGoctadXGoctadE18nGT12Nums, 2048), (wGoctadXGoctadE18nGT13Labs, wGoctadXGoctadE18nGT13Nums,
    2048), (wGoctadXGoctadE18nGT14Labs, wGoctadXGoctadE18nGT14Nums, 2048),
    (wGoctadXGoctadE18nGT15Labs, wGoctadXGoctadE18nGT15Nums, 2048), (wGoctadXGoctadE18nGT16Labs,
    wGoctadXGoctadE18nGT16Nums, 2048), (wGoctadXGoctadE18nGT17Labs, wGoctadXGoctadE18nGT17Nums,
    2048), (wGoctadXGoctadE18nGT18Labs, wGoctadXGoctadE18nGT18Nums, 2048),
    (wGoctadXGoctadE18nGT19Labs, wGoctadXGoctadE18nGT19Nums, 2048), (wGoctadXGoctadE18nGT20Labs,
    wGoctadXGoctadE18nGT20Nums, 2048), (wGoctadXGoctadE18nGT21Labs, wGoctadXGoctadE18nGT21Nums,
    2048), (wGoctadXGoctadE18nGT22Labs, wGoctadXGoctadE18nGT22Nums, 1026)] 512448 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGoctadXGoctadE18n_hn : wGoctadXGoctadE18nL.sden * (octSumZ 64 false wGoctadXGoctadE18nL
    wGoctadXGoctadE18nW : ℚ) / 8 =
    wGoctadXGoctadE18nW.sden * (selfOctP wGoctadXGoctadE18nW : ℚ) := by
  rw [wGoctadXGoctadE18n_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGoctadXGoctadE18nW _
      512448 wGoctadXGoctadE18n_Wsh wGoctadXGoctadE18n_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
