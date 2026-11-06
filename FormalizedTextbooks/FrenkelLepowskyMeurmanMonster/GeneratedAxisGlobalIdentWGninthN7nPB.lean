/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN7nChecks
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
theorem wGninthN7n_chk : OctadDense.octSumChk 64 6 false [(wGninthN7nHT0Labs, wGninthN7nHT0Nums,
    2048), (wGninthN7nHT1Labs, wGninthN7nHT1Nums, 2048), (wGninthN7nHT2Labs, wGninthN7nHT2Nums,
    2048), (wGninthN7nHT3Labs, wGninthN7nHT3Nums, 2048), (wGninthN7nHT4Labs, wGninthN7nHT4Nums,
    2048), (wGninthN7nHT5Labs, wGninthN7nHT5Nums, 2048), (wGninthN7nHT6Labs, wGninthN7nHT6Nums,
    2048), (wGninthN7nHT7Labs, wGninthN7nHT7Nums, 2048), (wGninthN7nHT8Labs, wGninthN7nHT8Nums,
    2048), (wGninthN7nHT9Labs, wGninthN7nHT9Nums, 2048), (wGninthN7nHT10Labs, wGninthN7nHT10Nums,
    2048), (wGninthN7nHT11Labs, wGninthN7nHT11Nums, 2048), (wGninthN7nHT12Labs,
    wGninthN7nHT12Nums, 2048), (wGninthN7nHT13Labs, wGninthN7nHT13Nums, 2048),
    (wGninthN7nHT14Labs, wGninthN7nHT14Nums, 2048), (wGninthN7nHT15Labs, wGninthN7nHT15Nums,
    2048), (wGninthN7nHT16Labs, wGninthN7nHT16Nums, 2048), (wGninthN7nHT17Labs,
    wGninthN7nHT17Nums, 2048), (wGninthN7nHT18Labs, wGninthN7nHT18Nums, 2048),
    (wGninthN7nHT19Labs, wGninthN7nHT19Nums, 2048), (wGninthN7nHT20Labs, wGninthN7nHT20Nums,
    2048), (wGninthN7nHT21Labs, wGninthN7nHT21Nums, 2048), (wGninthN7nHT22Labs,
    wGninthN7nHT22Nums, 2048), (wGninthN7nHT23Labs, wGninthN7nHT23Nums, 2048),
    (wGninthN7nHT24Labs, wGninthN7nHT24Nums, 2048), (wGninthN7nHT25Labs, wGninthN7nHT25Nums,
    2048), (wGninthN7nHT26Labs, wGninthN7nHT26Nums, 2048), (wGninthN7nHT27Labs,
    wGninthN7nHT27Nums, 2048), (wGninthN7nHT28Labs, wGninthN7nHT28Nums, 2048),
    (wGninthN7nHT29Labs, wGninthN7nHT29Nums, 2048), (wGninthN7nHT30Labs, wGninthN7nHT30Nums, 144)]
    [(wGninthN7nGT0Labs, wGninthN7nGT0Nums, 2048), (wGninthN7nGT1Labs, wGninthN7nGT1Nums, 2048),
    (wGninthN7nGT2Labs, wGninthN7nGT2Nums, 40)] 491520 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGninthN7n_Lsh : wGninthN7nL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN7nHT0Labs, wGninthN7nHT0Nums, 2048), (wGninthN7nHT1Labs, wGninthN7nHT1Nums, 2048),
    (wGninthN7nHT2Labs, wGninthN7nHT2Nums, 2048), (wGninthN7nHT3Labs, wGninthN7nHT3Nums, 2048),
    (wGninthN7nHT4Labs, wGninthN7nHT4Nums, 2048), (wGninthN7nHT5Labs, wGninthN7nHT5Nums, 2048),
    (wGninthN7nHT6Labs, wGninthN7nHT6Nums, 2048), (wGninthN7nHT7Labs, wGninthN7nHT7Nums, 2048),
    (wGninthN7nHT8Labs, wGninthN7nHT8Nums, 2048), (wGninthN7nHT9Labs, wGninthN7nHT9Nums, 2048),
    (wGninthN7nHT10Labs, wGninthN7nHT10Nums, 2048), (wGninthN7nHT11Labs, wGninthN7nHT11Nums,
    2048), (wGninthN7nHT12Labs, wGninthN7nHT12Nums, 2048), (wGninthN7nHT13Labs,
    wGninthN7nHT13Nums, 2048), (wGninthN7nHT14Labs, wGninthN7nHT14Nums, 2048),
    (wGninthN7nHT15Labs, wGninthN7nHT15Nums, 2048), (wGninthN7nHT16Labs, wGninthN7nHT16Nums,
    2048), (wGninthN7nHT17Labs, wGninthN7nHT17Nums, 2048), (wGninthN7nHT18Labs,
    wGninthN7nHT18Nums, 2048), (wGninthN7nHT19Labs, wGninthN7nHT19Nums, 2048),
    (wGninthN7nHT20Labs, wGninthN7nHT20Nums, 2048), (wGninthN7nHT21Labs, wGninthN7nHT21Nums,
    2048), (wGninthN7nHT22Labs, wGninthN7nHT22Nums, 2048), (wGninthN7nHT23Labs,
    wGninthN7nHT23Nums, 2048), (wGninthN7nHT24Labs, wGninthN7nHT24Nums, 2048),
    (wGninthN7nHT25Labs, wGninthN7nHT25Nums, 2048), (wGninthN7nHT26Labs, wGninthN7nHT26Nums,
    2048), (wGninthN7nHT27Labs, wGninthN7nHT27Nums, 2048), (wGninthN7nHT28Labs,
    wGninthN7nHT28Nums, 2048), (wGninthN7nHT29Labs, wGninthN7nHT29Nums, 2048),
    (wGninthN7nHT30Labs, wGninthN7nHT30Nums, 144)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGninthN7n_Wsh : wGninthN7nW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN7nGT0Labs, wGninthN7nGT0Nums, 2048), (wGninthN7nGT1Labs, wGninthN7nGT1Nums, 2048),
    (wGninthN7nGT2Labs, wGninthN7nGT2Nums, 40)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGninthN7n_hok : octPackOk 64 wGninthN7nL = true :=
  OctadDense.octPackOk_of_chk 64 6 false wGninthN7nL _ _ 491520 wGninthN7n_Lsh wGninthN7n_chk

/-- The octad integer sum. -/
theorem wGninthN7n_octn : octSumZ 64 false wGninthN7nL wGninthN7nW = 491520 :=
  OctadDense.octSumZ_of_chk 64 6 false wGninthN7nL wGninthN7nW _ _ 491520 wGninthN7n_Lsh
      wGninthN7n_Wsh wGninthN7n_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGninthN7n_selfchk : OctadDense.selfOctChk 64 [(wGninthN7nGT0Labs, wGninthN7nGT0Nums,
    2048), (wGninthN7nGT1Labs, wGninthN7nGT1Nums, 2048), (wGninthN7nGT2Labs, wGninthN7nGT2Nums,
    40)] 7680 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGninthN7n_hn : wGninthN7nL.sden * (octSumZ 64 false wGninthN7nL wGninthN7nW : ℚ) / 8 =
    wGninthN7nW.sden * (selfOctP wGninthN7nW : ℚ) := by
  rw [wGninthN7n_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGninthN7nW _ 7680
      wGninthN7n_Wsh wGninthN7n_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
