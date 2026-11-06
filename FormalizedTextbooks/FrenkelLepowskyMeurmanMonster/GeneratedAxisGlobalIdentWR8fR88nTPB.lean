/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR88nTChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octads) of the identification Root8[20]- <-> Tenth[69]+ (record r8f:R88-, e =
-1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wR8fR88nT_chk : OctadDense.octSumChk 64 6 false [(wR8fR88nTHT0Labs, wR8fR88nTHT0Nums,
    2048), (wR8fR88nTHT1Labs, wR8fR88nTHT1Nums, 2048), (wR8fR88nTHT2Labs, wR8fR88nTHT2Nums, 2048),
    (wR8fR88nTHT3Labs, wR8fR88nTHT3Nums, 2048), (wR8fR88nTHT4Labs, wR8fR88nTHT4Nums, 2048),
    (wR8fR88nTHT5Labs, wR8fR88nTHT5Nums, 2048), (wR8fR88nTHT6Labs, wR8fR88nTHT6Nums, 2048),
    (wR8fR88nTHT7Labs, wR8fR88nTHT7Nums, 2048), (wR8fR88nTHT8Labs, wR8fR88nTHT8Nums, 2048),
    (wR8fR88nTHT9Labs, wR8fR88nTHT9Nums, 2048), (wR8fR88nTHT10Labs, wR8fR88nTHT10Nums, 2048),
    (wR8fR88nTHT11Labs, wR8fR88nTHT11Nums, 2048), (wR8fR88nTHT12Labs, wR8fR88nTHT12Nums, 2048),
    (wR8fR88nTHT13Labs, wR8fR88nTHT13Nums, 2048), (wR8fR88nTHT14Labs, wR8fR88nTHT14Nums, 2048),
    (wR8fR88nTHT15Labs, wR8fR88nTHT15Nums, 2048), (wR8fR88nTHT16Labs, wR8fR88nTHT16Nums, 808)]
    [(wR8fR88nTGT0Labs, wR8fR88nTGT0Nums, 2048), (wR8fR88nTGT1Labs, wR8fR88nTGT1Nums, 2048),
    (wR8fR88nTGT2Labs, wR8fR88nTGT2Nums, 2048), (wR8fR88nTGT3Labs, wR8fR88nTGT3Nums, 2048),
    (wR8fR88nTGT4Labs, wR8fR88nTGT4Nums, 2048), (wR8fR88nTGT5Labs, wR8fR88nTGT5Nums, 2048),
    (wR8fR88nTGT6Labs, wR8fR88nTGT6Nums, 2048), (wR8fR88nTGT7Labs, wR8fR88nTGT7Nums, 2048),
    (wR8fR88nTGT8Labs, wR8fR88nTGT8Nums, 2048), (wR8fR88nTGT9Labs, wR8fR88nTGT9Nums, 2048),
    (wR8fR88nTGT10Labs, wR8fR88nTGT10Nums, 2048), (wR8fR88nTGT11Labs, wR8fR88nTGT11Nums, 2048),
    (wR8fR88nTGT12Labs, wR8fR88nTGT12Nums, 2048), (wR8fR88nTGT13Labs, wR8fR88nTGT13Nums, 2048),
    (wR8fR88nTGT14Labs, wR8fR88nTGT14Nums, 2048), (wR8fR88nTGT15Labs, wR8fR88nTGT15Nums, 2048),
    (wR8fR88nTGT16Labs, wR8fR88nTGT16Nums, 2048), (wR8fR88nTGT17Labs, wR8fR88nTGT17Nums, 2048),
    (wR8fR88nTGT18Labs, wR8fR88nTGT18Nums, 2048), (wR8fR88nTGT19Labs, wR8fR88nTGT19Nums, 2048),
    (wR8fR88nTGT20Labs, wR8fR88nTGT20Nums, 2048), (wR8fR88nTGT21Labs, wR8fR88nTGT21Nums, 2048),
    (wR8fR88nTGT22Labs, wR8fR88nTGT22Nums, 1026)] 4017152 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wR8fR88nT_Lsh : wR8fR88nTL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR88nTHT0Labs, wR8fR88nTHT0Nums, 2048), (wR8fR88nTHT1Labs, wR8fR88nTHT1Nums, 2048),
    (wR8fR88nTHT2Labs, wR8fR88nTHT2Nums, 2048), (wR8fR88nTHT3Labs, wR8fR88nTHT3Nums, 2048),
    (wR8fR88nTHT4Labs, wR8fR88nTHT4Nums, 2048), (wR8fR88nTHT5Labs, wR8fR88nTHT5Nums, 2048),
    (wR8fR88nTHT6Labs, wR8fR88nTHT6Nums, 2048), (wR8fR88nTHT7Labs, wR8fR88nTHT7Nums, 2048),
    (wR8fR88nTHT8Labs, wR8fR88nTHT8Nums, 2048), (wR8fR88nTHT9Labs, wR8fR88nTHT9Nums, 2048),
    (wR8fR88nTHT10Labs, wR8fR88nTHT10Nums, 2048), (wR8fR88nTHT11Labs, wR8fR88nTHT11Nums, 2048),
    (wR8fR88nTHT12Labs, wR8fR88nTHT12Nums, 2048), (wR8fR88nTHT13Labs, wR8fR88nTHT13Nums, 2048),
    (wR8fR88nTHT14Labs, wR8fR88nTHT14Nums, 2048), (wR8fR88nTHT15Labs, wR8fR88nTHT15Nums, 2048),
    (wR8fR88nTHT16Labs, wR8fR88nTHT16Nums, 808)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wR8fR88nT_Wsh : wR8fR88nTW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR88nTGT0Labs, wR8fR88nTGT0Nums, 2048), (wR8fR88nTGT1Labs, wR8fR88nTGT1Nums, 2048),
    (wR8fR88nTGT2Labs, wR8fR88nTGT2Nums, 2048), (wR8fR88nTGT3Labs, wR8fR88nTGT3Nums, 2048),
    (wR8fR88nTGT4Labs, wR8fR88nTGT4Nums, 2048), (wR8fR88nTGT5Labs, wR8fR88nTGT5Nums, 2048),
    (wR8fR88nTGT6Labs, wR8fR88nTGT6Nums, 2048), (wR8fR88nTGT7Labs, wR8fR88nTGT7Nums, 2048),
    (wR8fR88nTGT8Labs, wR8fR88nTGT8Nums, 2048), (wR8fR88nTGT9Labs, wR8fR88nTGT9Nums, 2048),
    (wR8fR88nTGT10Labs, wR8fR88nTGT10Nums, 2048), (wR8fR88nTGT11Labs, wR8fR88nTGT11Nums, 2048),
    (wR8fR88nTGT12Labs, wR8fR88nTGT12Nums, 2048), (wR8fR88nTGT13Labs, wR8fR88nTGT13Nums, 2048),
    (wR8fR88nTGT14Labs, wR8fR88nTGT14Nums, 2048), (wR8fR88nTGT15Labs, wR8fR88nTGT15Nums, 2048),
    (wR8fR88nTGT16Labs, wR8fR88nTGT16Nums, 2048), (wR8fR88nTGT17Labs, wR8fR88nTGT17Nums, 2048),
    (wR8fR88nTGT18Labs, wR8fR88nTGT18Nums, 2048), (wR8fR88nTGT19Labs, wR8fR88nTGT19Nums, 2048),
    (wR8fR88nTGT20Labs, wR8fR88nTGT20Nums, 2048), (wR8fR88nTGT21Labs, wR8fR88nTGT21Nums, 2048),
    (wR8fR88nTGT22Labs, wR8fR88nTGT22Nums, 1026)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wR8fR88nT_hok : octPackOk 64 wR8fR88nTL = true :=
  OctadDense.octPackOk_of_chk 64 6 false wR8fR88nTL _ _ 4017152 wR8fR88nT_Lsh wR8fR88nT_chk

/-- The octad integer sum. -/
theorem wR8fR88nT_octn : octSumZ 64 false wR8fR88nTL wR8fR88nTW = 4017152 :=
  OctadDense.octSumZ_of_chk 64 6 false wR8fR88nTL wR8fR88nTW _ _ 4017152 wR8fR88nT_Lsh
      wR8fR88nT_Wsh wR8fR88nT_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wR8fR88nT_selfchk : OctadDense.selfOctChk 64 [(wR8fR88nTGT0Labs, wR8fR88nTGT0Nums, 2048),
    (wR8fR88nTGT1Labs, wR8fR88nTGT1Nums, 2048), (wR8fR88nTGT2Labs, wR8fR88nTGT2Nums, 2048),
    (wR8fR88nTGT3Labs, wR8fR88nTGT3Nums, 2048), (wR8fR88nTGT4Labs, wR8fR88nTGT4Nums, 2048),
    (wR8fR88nTGT5Labs, wR8fR88nTGT5Nums, 2048), (wR8fR88nTGT6Labs, wR8fR88nTGT6Nums, 2048),
    (wR8fR88nTGT7Labs, wR8fR88nTGT7Nums, 2048), (wR8fR88nTGT8Labs, wR8fR88nTGT8Nums, 2048),
    (wR8fR88nTGT9Labs, wR8fR88nTGT9Nums, 2048), (wR8fR88nTGT10Labs, wR8fR88nTGT10Nums, 2048),
    (wR8fR88nTGT11Labs, wR8fR88nTGT11Nums, 2048), (wR8fR88nTGT12Labs, wR8fR88nTGT12Nums, 2048),
    (wR8fR88nTGT13Labs, wR8fR88nTGT13Nums, 2048), (wR8fR88nTGT14Labs, wR8fR88nTGT14Nums, 2048),
    (wR8fR88nTGT15Labs, wR8fR88nTGT15Nums, 2048), (wR8fR88nTGT16Labs, wR8fR88nTGT16Nums, 2048),
    (wR8fR88nTGT17Labs, wR8fR88nTGT17Nums, 2048), (wR8fR88nTGT18Labs, wR8fR88nTGT18Nums, 2048),
    (wR8fR88nTGT19Labs, wR8fR88nTGT19Nums, 2048), (wR8fR88nTGT20Labs, wR8fR88nTGT20Nums, 2048),
    (wR8fR88nTGT21Labs, wR8fR88nTGT21Nums, 2048), (wR8fR88nTGT22Labs, wR8fR88nTGT22Nums, 1026)]
    502144 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wR8fR88nT_hn : wR8fR88nTL.sden * (octSumZ 64 false wR8fR88nTL wR8fR88nTW : ℚ) / 8 =
    wR8fR88nTW.sden * (selfOctP wR8fR88nTW : ℚ) := by
  rw [wR8fR88nT_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wR8fR88nTW _ 502144 wR8fR88nT_Wsh
      wR8fR88nT_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
