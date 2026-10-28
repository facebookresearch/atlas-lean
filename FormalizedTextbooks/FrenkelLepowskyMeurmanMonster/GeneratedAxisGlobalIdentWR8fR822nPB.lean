/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR822nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Factory parts (octads) of the identification Root8[4]- <-> Root8[4]- (record r8f:R822-, e =
-1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wR8fR822n_chk : OctadDense.octSumChk 64 6 false [(wR8fR822nHT0Labs, wR8fR822nHT0Nums,
    2048), (wR8fR822nHT1Labs, wR8fR822nHT1Nums, 2048), (wR8fR822nHT2Labs, wR8fR822nHT2Nums, 2048),
    (wR8fR822nHT3Labs, wR8fR822nHT3Nums, 2048), (wR8fR822nHT4Labs, wR8fR822nHT4Nums, 2048),
    (wR8fR822nHT5Labs, wR8fR822nHT5Nums, 2048), (wR8fR822nHT6Labs, wR8fR822nHT6Nums, 2048),
    (wR8fR822nHT7Labs, wR8fR822nHT7Nums, 2048), (wR8fR822nHT8Labs, wR8fR822nHT8Nums, 2048),
    (wR8fR822nHT9Labs, wR8fR822nHT9Nums, 2048), (wR8fR822nHT10Labs, wR8fR822nHT10Nums, 2048),
    (wR8fR822nHT11Labs, wR8fR822nHT11Nums, 2048), (wR8fR822nHT12Labs, wR8fR822nHT12Nums, 2048),
    (wR8fR822nHT13Labs, wR8fR822nHT13Nums, 2048), (wR8fR822nHT14Labs, wR8fR822nHT14Nums, 2048),
    (wR8fR822nHT15Labs, wR8fR822nHT15Nums, 2048), (wR8fR822nHT16Labs, wR8fR822nHT16Nums, 808)]
    [(wR8fR822nGT0Labs, wR8fR822nGT0Nums, 2048), (wR8fR822nGT1Labs, wR8fR822nGT1Nums, 2048),
    (wR8fR822nGT2Labs, wR8fR822nGT2Nums, 2048), (wR8fR822nGT3Labs, wR8fR822nGT3Nums, 2048),
    (wR8fR822nGT4Labs, wR8fR822nGT4Nums, 2048), (wR8fR822nGT5Labs, wR8fR822nGT5Nums, 2048),
    (wR8fR822nGT6Labs, wR8fR822nGT6Nums, 2048), (wR8fR822nGT7Labs, wR8fR822nGT7Nums, 2048),
    (wR8fR822nGT8Labs, wR8fR822nGT8Nums, 2048), (wR8fR822nGT9Labs, wR8fR822nGT9Nums, 2048),
    (wR8fR822nGT10Labs, wR8fR822nGT10Nums, 2048), (wR8fR822nGT11Labs, wR8fR822nGT11Nums, 2048),
    (wR8fR822nGT12Labs, wR8fR822nGT12Nums, 2048), (wR8fR822nGT13Labs, wR8fR822nGT13Nums, 2048),
    (wR8fR822nGT14Labs, wR8fR822nGT14Nums, 2048), (wR8fR822nGT15Labs, wR8fR822nGT15Nums, 2048),
    (wR8fR822nGT16Labs, wR8fR822nGT16Nums, 808)] 3993088 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wR8fR822n_Lsh : wR8fR822nL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR822nHT0Labs, wR8fR822nHT0Nums, 2048), (wR8fR822nHT1Labs, wR8fR822nHT1Nums, 2048),
    (wR8fR822nHT2Labs, wR8fR822nHT2Nums, 2048), (wR8fR822nHT3Labs, wR8fR822nHT3Nums, 2048),
    (wR8fR822nHT4Labs, wR8fR822nHT4Nums, 2048), (wR8fR822nHT5Labs, wR8fR822nHT5Nums, 2048),
    (wR8fR822nHT6Labs, wR8fR822nHT6Nums, 2048), (wR8fR822nHT7Labs, wR8fR822nHT7Nums, 2048),
    (wR8fR822nHT8Labs, wR8fR822nHT8Nums, 2048), (wR8fR822nHT9Labs, wR8fR822nHT9Nums, 2048),
    (wR8fR822nHT10Labs, wR8fR822nHT10Nums, 2048), (wR8fR822nHT11Labs, wR8fR822nHT11Nums, 2048),
    (wR8fR822nHT12Labs, wR8fR822nHT12Nums, 2048), (wR8fR822nHT13Labs, wR8fR822nHT13Nums, 2048),
    (wR8fR822nHT14Labs, wR8fR822nHT14Nums, 2048), (wR8fR822nHT15Labs, wR8fR822nHT15Nums, 2048),
    (wR8fR822nHT16Labs, wR8fR822nHT16Nums, 808)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wR8fR822n_Wsh : wR8fR822nW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR822nGT0Labs, wR8fR822nGT0Nums, 2048), (wR8fR822nGT1Labs, wR8fR822nGT1Nums, 2048),
    (wR8fR822nGT2Labs, wR8fR822nGT2Nums, 2048), (wR8fR822nGT3Labs, wR8fR822nGT3Nums, 2048),
    (wR8fR822nGT4Labs, wR8fR822nGT4Nums, 2048), (wR8fR822nGT5Labs, wR8fR822nGT5Nums, 2048),
    (wR8fR822nGT6Labs, wR8fR822nGT6Nums, 2048), (wR8fR822nGT7Labs, wR8fR822nGT7Nums, 2048),
    (wR8fR822nGT8Labs, wR8fR822nGT8Nums, 2048), (wR8fR822nGT9Labs, wR8fR822nGT9Nums, 2048),
    (wR8fR822nGT10Labs, wR8fR822nGT10Nums, 2048), (wR8fR822nGT11Labs, wR8fR822nGT11Nums, 2048),
    (wR8fR822nGT12Labs, wR8fR822nGT12Nums, 2048), (wR8fR822nGT13Labs, wR8fR822nGT13Nums, 2048),
    (wR8fR822nGT14Labs, wR8fR822nGT14Nums, 2048), (wR8fR822nGT15Labs, wR8fR822nGT15Nums, 2048),
    (wR8fR822nGT16Labs, wR8fR822nGT16Nums, 808)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wR8fR822n_hok : octPackOk 64 wR8fR822nL = true :=
  OctadDense.octPackOk_of_chk 64 6 false wR8fR822nL _ _ 3993088 wR8fR822n_Lsh wR8fR822n_chk

/-- The octad integer sum. -/
theorem wR8fR822n_octn : octSumZ 64 false wR8fR822nL wR8fR822nW = 3993088 :=
  OctadDense.octSumZ_of_chk 64 6 false wR8fR822nL wR8fR822nW _ _ 3993088 wR8fR822n_Lsh
      wR8fR822n_Wsh wR8fR822n_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wR8fR822n_selfchk : OctadDense.selfOctChk 64 [(wR8fR822nGT0Labs, wR8fR822nGT0Nums, 2048),
    (wR8fR822nGT1Labs, wR8fR822nGT1Nums, 2048), (wR8fR822nGT2Labs, wR8fR822nGT2Nums, 2048),
    (wR8fR822nGT3Labs, wR8fR822nGT3Nums, 2048), (wR8fR822nGT4Labs, wR8fR822nGT4Nums, 2048),
    (wR8fR822nGT5Labs, wR8fR822nGT5Nums, 2048), (wR8fR822nGT6Labs, wR8fR822nGT6Nums, 2048),
    (wR8fR822nGT7Labs, wR8fR822nGT7Nums, 2048), (wR8fR822nGT8Labs, wR8fR822nGT8Nums, 2048),
    (wR8fR822nGT9Labs, wR8fR822nGT9Nums, 2048), (wR8fR822nGT10Labs, wR8fR822nGT10Nums, 2048),
    (wR8fR822nGT11Labs, wR8fR822nGT11Nums, 2048), (wR8fR822nGT12Labs, wR8fR822nGT12Nums, 2048),
    (wR8fR822nGT13Labs, wR8fR822nGT13Nums, 2048), (wR8fR822nGT14Labs, wR8fR822nGT14Nums, 2048),
    (wR8fR822nGT15Labs, wR8fR822nGT15Nums, 2048), (wR8fR822nGT16Labs, wR8fR822nGT16Nums, 808)]
    499136 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wR8fR822n_hn : wR8fR822nL.sden * (octSumZ 64 false wR8fR822nL wR8fR822nW : ℚ) / 8 =
    wR8fR822nW.sden * (selfOctP wR8fR822nW : ℚ) := by
  rw [wR8fR822n_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wR8fR822nW _ 499136 wR8fR822n_Wsh
      wR8fR822n_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
