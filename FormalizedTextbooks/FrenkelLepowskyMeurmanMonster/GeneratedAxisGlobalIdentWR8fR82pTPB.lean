/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR82pTChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT

/-! # Factory parts (octads) of the identification Eighth[18]- <-> Root8[2]+ (record r8f:R82+, e =
1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wR8fR82pT_chk : OctadDense.octSumChk 64 6 true [(wR8fR82pTHT0Labs, wR8fR82pTHT0Nums,
    2048), (wR8fR82pTHT1Labs, wR8fR82pTHT1Nums, 2048), (wR8fR82pTHT2Labs, wR8fR82pTHT2Nums, 2048),
    (wR8fR82pTHT3Labs, wR8fR82pTHT3Nums, 2048), (wR8fR82pTHT4Labs, wR8fR82pTHT4Nums, 2048),
    (wR8fR82pTHT5Labs, wR8fR82pTHT5Nums, 2048), (wR8fR82pTHT6Labs, wR8fR82pTHT6Nums, 2048),
    (wR8fR82pTHT7Labs, wR8fR82pTHT7Nums, 2048), (wR8fR82pTHT8Labs, wR8fR82pTHT8Nums, 2048),
    (wR8fR82pTHT9Labs, wR8fR82pTHT9Nums, 2048), (wR8fR82pTHT10Labs, wR8fR82pTHT10Nums, 2048),
    (wR8fR82pTHT11Labs, wR8fR82pTHT11Nums, 2048), (wR8fR82pTHT12Labs, wR8fR82pTHT12Nums, 2048),
    (wR8fR82pTHT13Labs, wR8fR82pTHT13Nums, 2048), (wR8fR82pTHT14Labs, wR8fR82pTHT14Nums, 2048),
    (wR8fR82pTHT15Labs, wR8fR82pTHT15Nums, 2048), (wR8fR82pTHT16Labs, wR8fR82pTHT16Nums, 808)]
    [(wR8fR82pTGT0Labs, wR8fR82pTGT0Nums, 2048), (wR8fR82pTGT1Labs, wR8fR82pTGT1Nums, 2048),
    (wR8fR82pTGT2Labs, wR8fR82pTGT2Nums, 2048), (wR8fR82pTGT3Labs, wR8fR82pTGT3Nums, 2048),
    (wR8fR82pTGT4Labs, wR8fR82pTGT4Nums, 2048), (wR8fR82pTGT5Labs, wR8fR82pTGT5Nums, 2048),
    (wR8fR82pTGT6Labs, wR8fR82pTGT6Nums, 2048), (wR8fR82pTGT7Labs, wR8fR82pTGT7Nums, 2048),
    (wR8fR82pTGT8Labs, wR8fR82pTGT8Nums, 2048), (wR8fR82pTGT9Labs, wR8fR82pTGT9Nums, 2048),
    (wR8fR82pTGT10Labs, wR8fR82pTGT10Nums, 2048), (wR8fR82pTGT11Labs, wR8fR82pTGT11Nums, 2048),
    (wR8fR82pTGT12Labs, wR8fR82pTGT12Nums, 2048), (wR8fR82pTGT13Labs, wR8fR82pTGT13Nums, 2048),
    (wR8fR82pTGT14Labs, wR8fR82pTGT14Nums, 2048), (wR8fR82pTGT15Labs, wR8fR82pTGT15Nums, 2048),
    (wR8fR82pTGT16Labs, wR8fR82pTGT16Nums, 2048), (wR8fR82pTGT17Labs, wR8fR82pTGT17Nums, 2048),
    (wR8fR82pTGT18Labs, wR8fR82pTGT18Nums, 2048), (wR8fR82pTGT19Labs, wR8fR82pTGT19Nums, 2048),
    (wR8fR82pTGT20Labs, wR8fR82pTGT20Nums, 2048), (wR8fR82pTGT21Labs, wR8fR82pTGT21Nums, 668)]
    1013632 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wR8fR82pT_Lsh : wR8fR82pTL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR82pTHT0Labs, wR8fR82pTHT0Nums, 2048), (wR8fR82pTHT1Labs, wR8fR82pTHT1Nums, 2048),
    (wR8fR82pTHT2Labs, wR8fR82pTHT2Nums, 2048), (wR8fR82pTHT3Labs, wR8fR82pTHT3Nums, 2048),
    (wR8fR82pTHT4Labs, wR8fR82pTHT4Nums, 2048), (wR8fR82pTHT5Labs, wR8fR82pTHT5Nums, 2048),
    (wR8fR82pTHT6Labs, wR8fR82pTHT6Nums, 2048), (wR8fR82pTHT7Labs, wR8fR82pTHT7Nums, 2048),
    (wR8fR82pTHT8Labs, wR8fR82pTHT8Nums, 2048), (wR8fR82pTHT9Labs, wR8fR82pTHT9Nums, 2048),
    (wR8fR82pTHT10Labs, wR8fR82pTHT10Nums, 2048), (wR8fR82pTHT11Labs, wR8fR82pTHT11Nums, 2048),
    (wR8fR82pTHT12Labs, wR8fR82pTHT12Nums, 2048), (wR8fR82pTHT13Labs, wR8fR82pTHT13Nums, 2048),
    (wR8fR82pTHT14Labs, wR8fR82pTHT14Nums, 2048), (wR8fR82pTHT15Labs, wR8fR82pTHT15Nums, 2048),
    (wR8fR82pTHT16Labs, wR8fR82pTHT16Nums, 808)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wR8fR82pT_Wsh : wR8fR82pTW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR82pTGT0Labs, wR8fR82pTGT0Nums, 2048), (wR8fR82pTGT1Labs, wR8fR82pTGT1Nums, 2048),
    (wR8fR82pTGT2Labs, wR8fR82pTGT2Nums, 2048), (wR8fR82pTGT3Labs, wR8fR82pTGT3Nums, 2048),
    (wR8fR82pTGT4Labs, wR8fR82pTGT4Nums, 2048), (wR8fR82pTGT5Labs, wR8fR82pTGT5Nums, 2048),
    (wR8fR82pTGT6Labs, wR8fR82pTGT6Nums, 2048), (wR8fR82pTGT7Labs, wR8fR82pTGT7Nums, 2048),
    (wR8fR82pTGT8Labs, wR8fR82pTGT8Nums, 2048), (wR8fR82pTGT9Labs, wR8fR82pTGT9Nums, 2048),
    (wR8fR82pTGT10Labs, wR8fR82pTGT10Nums, 2048), (wR8fR82pTGT11Labs, wR8fR82pTGT11Nums, 2048),
    (wR8fR82pTGT12Labs, wR8fR82pTGT12Nums, 2048), (wR8fR82pTGT13Labs, wR8fR82pTGT13Nums, 2048),
    (wR8fR82pTGT14Labs, wR8fR82pTGT14Nums, 2048), (wR8fR82pTGT15Labs, wR8fR82pTGT15Nums, 2048),
    (wR8fR82pTGT16Labs, wR8fR82pTGT16Nums, 2048), (wR8fR82pTGT17Labs, wR8fR82pTGT17Nums, 2048),
    (wR8fR82pTGT18Labs, wR8fR82pTGT18Nums, 2048), (wR8fR82pTGT19Labs, wR8fR82pTGT19Nums, 2048),
    (wR8fR82pTGT20Labs, wR8fR82pTGT20Nums, 2048), (wR8fR82pTGT21Labs, wR8fR82pTGT21Nums, 668)]) :=
    by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wR8fR82pT_hok : octPackOk 64 wR8fR82pTL = true :=
  OctadDense.octPackOk_of_chk 64 6 true wR8fR82pTL _ _ 1013632 wR8fR82pT_Lsh wR8fR82pT_chk

/-- The octad integer sum. -/
theorem wR8fR82pT_octn : octSumZ 64 true wR8fR82pTL wR8fR82pTW = 1013632 :=
  OctadDense.octSumZ_of_chk 64 6 true wR8fR82pTL wR8fR82pTW _ _ 1013632 wR8fR82pT_Lsh
      wR8fR82pT_Wsh wR8fR82pT_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wR8fR82pT_selfchk : OctadDense.selfOctChk 64 [(wR8fR82pTGT0Labs, wR8fR82pTGT0Nums, 2048),
    (wR8fR82pTGT1Labs, wR8fR82pTGT1Nums, 2048), (wR8fR82pTGT2Labs, wR8fR82pTGT2Nums, 2048),
    (wR8fR82pTGT3Labs, wR8fR82pTGT3Nums, 2048), (wR8fR82pTGT4Labs, wR8fR82pTGT4Nums, 2048),
    (wR8fR82pTGT5Labs, wR8fR82pTGT5Nums, 2048), (wR8fR82pTGT6Labs, wR8fR82pTGT6Nums, 2048),
    (wR8fR82pTGT7Labs, wR8fR82pTGT7Nums, 2048), (wR8fR82pTGT8Labs, wR8fR82pTGT8Nums, 2048),
    (wR8fR82pTGT9Labs, wR8fR82pTGT9Nums, 2048), (wR8fR82pTGT10Labs, wR8fR82pTGT10Nums, 2048),
    (wR8fR82pTGT11Labs, wR8fR82pTGT11Nums, 2048), (wR8fR82pTGT12Labs, wR8fR82pTGT12Nums, 2048),
    (wR8fR82pTGT13Labs, wR8fR82pTGT13Nums, 2048), (wR8fR82pTGT14Labs, wR8fR82pTGT14Nums, 2048),
    (wR8fR82pTGT15Labs, wR8fR82pTGT15Nums, 2048), (wR8fR82pTGT16Labs, wR8fR82pTGT16Nums, 2048),
    (wR8fR82pTGT17Labs, wR8fR82pTGT17Nums, 2048), (wR8fR82pTGT18Labs, wR8fR82pTGT18Nums, 2048),
    (wR8fR82pTGT19Labs, wR8fR82pTGT19Nums, 2048), (wR8fR82pTGT20Labs, wR8fR82pTGT20Nums, 2048),
    (wR8fR82pTGT21Labs, wR8fR82pTGT21Nums, 668)] 31676 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wR8fR82pT_hn : wR8fR82pTL.sden * (octSumZ 64 true wR8fR82pTL wR8fR82pTW : ℚ) / 8 =
    wR8fR82pTW.sden * (selfOctP wR8fR82pTW : ℚ) := by
  rw [wR8fR82pT_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wR8fR82pTW _ 31676 wR8fR82pT_Wsh
      wR8fR82pT_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
