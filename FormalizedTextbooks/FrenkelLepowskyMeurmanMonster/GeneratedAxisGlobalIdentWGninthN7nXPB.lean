/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN7nXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ

/-! # Factory parts (octads) of the identification Fifth[4]+ <-> Ninth[12]- (record gninth:N7-, e
= -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGninthN7nX_chk : OctadDense.octSumChk 64 6 false [(wGninthN7nXHT0Labs,
    wGninthN7nXHT0Nums, 2048), (wGninthN7nXHT1Labs, wGninthN7nXHT1Nums, 2048),
    (wGninthN7nXHT2Labs, wGninthN7nXHT2Nums, 2048), (wGninthN7nXHT3Labs, wGninthN7nXHT3Nums,
    2048), (wGninthN7nXHT4Labs, wGninthN7nXHT4Nums, 2048), (wGninthN7nXHT5Labs,
    wGninthN7nXHT5Nums, 2048), (wGninthN7nXHT6Labs, wGninthN7nXHT6Nums, 2048),
    (wGninthN7nXHT7Labs, wGninthN7nXHT7Nums, 2048), (wGninthN7nXHT8Labs, wGninthN7nXHT8Nums,
    2048), (wGninthN7nXHT9Labs, wGninthN7nXHT9Nums, 2048), (wGninthN7nXHT10Labs,
    wGninthN7nXHT10Nums, 2048), (wGninthN7nXHT11Labs, wGninthN7nXHT11Nums, 2048),
    (wGninthN7nXHT12Labs, wGninthN7nXHT12Nums, 2048), (wGninthN7nXHT13Labs, wGninthN7nXHT13Nums,
    2048), (wGninthN7nXHT14Labs, wGninthN7nXHT14Nums, 2048), (wGninthN7nXHT15Labs,
    wGninthN7nXHT15Nums, 2048), (wGninthN7nXHT16Labs, wGninthN7nXHT16Nums, 2048),
    (wGninthN7nXHT17Labs, wGninthN7nXHT17Nums, 2048), (wGninthN7nXHT18Labs, wGninthN7nXHT18Nums,
    2048), (wGninthN7nXHT19Labs, wGninthN7nXHT19Nums, 2048), (wGninthN7nXHT20Labs,
    wGninthN7nXHT20Nums, 2048), (wGninthN7nXHT21Labs, wGninthN7nXHT21Nums, 2048),
    (wGninthN7nXHT22Labs, wGninthN7nXHT22Nums, 2048), (wGninthN7nXHT23Labs, wGninthN7nXHT23Nums,
    2048), (wGninthN7nXHT24Labs, wGninthN7nXHT24Nums, 2048), (wGninthN7nXHT25Labs,
    wGninthN7nXHT25Nums, 2048), (wGninthN7nXHT26Labs, wGninthN7nXHT26Nums, 2048),
    (wGninthN7nXHT27Labs, wGninthN7nXHT27Nums, 2048), (wGninthN7nXHT28Labs, wGninthN7nXHT28Nums,
    2048), (wGninthN7nXHT29Labs, wGninthN7nXHT29Nums, 2048), (wGninthN7nXHT30Labs,
    wGninthN7nXHT30Nums, 144)] [(wGninthN7nXGT0Labs, wGninthN7nXGT0Nums, 2048),
    (wGninthN7nXGT1Labs, wGninthN7nXGT1Nums, 2048), (wGninthN7nXGT2Labs, wGninthN7nXGT2Nums, 40)]
    491520 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGninthN7nX_Lsh : wGninthN7nXL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN7nXHT0Labs, wGninthN7nXHT0Nums, 2048), (wGninthN7nXHT1Labs, wGninthN7nXHT1Nums,
    2048), (wGninthN7nXHT2Labs, wGninthN7nXHT2Nums, 2048), (wGninthN7nXHT3Labs,
    wGninthN7nXHT3Nums, 2048), (wGninthN7nXHT4Labs, wGninthN7nXHT4Nums, 2048),
    (wGninthN7nXHT5Labs, wGninthN7nXHT5Nums, 2048), (wGninthN7nXHT6Labs, wGninthN7nXHT6Nums,
    2048), (wGninthN7nXHT7Labs, wGninthN7nXHT7Nums, 2048), (wGninthN7nXHT8Labs,
    wGninthN7nXHT8Nums, 2048), (wGninthN7nXHT9Labs, wGninthN7nXHT9Nums, 2048),
    (wGninthN7nXHT10Labs, wGninthN7nXHT10Nums, 2048), (wGninthN7nXHT11Labs, wGninthN7nXHT11Nums,
    2048), (wGninthN7nXHT12Labs, wGninthN7nXHT12Nums, 2048), (wGninthN7nXHT13Labs,
    wGninthN7nXHT13Nums, 2048), (wGninthN7nXHT14Labs, wGninthN7nXHT14Nums, 2048),
    (wGninthN7nXHT15Labs, wGninthN7nXHT15Nums, 2048), (wGninthN7nXHT16Labs, wGninthN7nXHT16Nums,
    2048), (wGninthN7nXHT17Labs, wGninthN7nXHT17Nums, 2048), (wGninthN7nXHT18Labs,
    wGninthN7nXHT18Nums, 2048), (wGninthN7nXHT19Labs, wGninthN7nXHT19Nums, 2048),
    (wGninthN7nXHT20Labs, wGninthN7nXHT20Nums, 2048), (wGninthN7nXHT21Labs, wGninthN7nXHT21Nums,
    2048), (wGninthN7nXHT22Labs, wGninthN7nXHT22Nums, 2048), (wGninthN7nXHT23Labs,
    wGninthN7nXHT23Nums, 2048), (wGninthN7nXHT24Labs, wGninthN7nXHT24Nums, 2048),
    (wGninthN7nXHT25Labs, wGninthN7nXHT25Nums, 2048), (wGninthN7nXHT26Labs, wGninthN7nXHT26Nums,
    2048), (wGninthN7nXHT27Labs, wGninthN7nXHT27Nums, 2048), (wGninthN7nXHT28Labs,
    wGninthN7nXHT28Nums, 2048), (wGninthN7nXHT29Labs, wGninthN7nXHT29Nums, 2048),
    (wGninthN7nXHT30Labs, wGninthN7nXHT30Nums, 144)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGninthN7nX_Wsh : wGninthN7nXW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN7nXGT0Labs, wGninthN7nXGT0Nums, 2048), (wGninthN7nXGT1Labs, wGninthN7nXGT1Nums,
    2048), (wGninthN7nXGT2Labs, wGninthN7nXGT2Nums, 40)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGninthN7nX_hok : octPackOk 64 wGninthN7nXL = true :=
  OctadDense.octPackOk_of_chk 64 6 false wGninthN7nXL _ _ 491520 wGninthN7nX_Lsh wGninthN7nX_chk

/-- The octad integer sum. -/
theorem wGninthN7nX_octn : octSumZ 64 false wGninthN7nXL wGninthN7nXW = 491520 :=
  OctadDense.octSumZ_of_chk 64 6 false wGninthN7nXL wGninthN7nXW _ _ 491520 wGninthN7nX_Lsh
      wGninthN7nX_Wsh wGninthN7nX_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGninthN7nX_selfchk : OctadDense.selfOctChk 64 [(wGninthN7nXGT0Labs, wGninthN7nXGT0Nums,
    2048), (wGninthN7nXGT1Labs, wGninthN7nXGT1Nums, 2048), (wGninthN7nXGT2Labs,
    wGninthN7nXGT2Nums, 40)] 7680 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGninthN7nX_hn : wGninthN7nXL.sden * (octSumZ 64 false wGninthN7nXL wGninthN7nXW : ℚ) / 8 =
    wGninthN7nXW.sden * (selfOctP wGninthN7nXW : ℚ) := by
  rw [wGninthN7nX_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGninthN7nXW _ 7680
      wGninthN7nX_Wsh wGninthN7nX_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
