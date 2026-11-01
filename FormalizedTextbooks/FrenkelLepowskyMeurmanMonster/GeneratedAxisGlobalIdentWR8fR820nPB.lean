/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR820nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcRootEightCF

/-! # Factory parts (octads) of the identification Root8[25]- <-> Root8[25]- (record r8f:R820-, e
= -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wR8fR820n_chk : OctadDense.octSumChk 64 6 false [(wR8fR820nHT0Labs, wR8fR820nHT0Nums,
    2048), (wR8fR820nHT1Labs, wR8fR820nHT1Nums, 2048), (wR8fR820nHT2Labs, wR8fR820nHT2Nums, 2048),
    (wR8fR820nHT3Labs, wR8fR820nHT3Nums, 2048), (wR8fR820nHT4Labs, wR8fR820nHT4Nums, 2048),
    (wR8fR820nHT5Labs, wR8fR820nHT5Nums, 2048), (wR8fR820nHT6Labs, wR8fR820nHT6Nums, 2048),
    (wR8fR820nHT7Labs, wR8fR820nHT7Nums, 2048), (wR8fR820nHT8Labs, wR8fR820nHT8Nums, 2048),
    (wR8fR820nHT9Labs, wR8fR820nHT9Nums, 2048), (wR8fR820nHT10Labs, wR8fR820nHT10Nums, 2048),
    (wR8fR820nHT11Labs, wR8fR820nHT11Nums, 2048), (wR8fR820nHT12Labs, wR8fR820nHT12Nums, 2048),
    (wR8fR820nHT13Labs, wR8fR820nHT13Nums, 2048), (wR8fR820nHT14Labs, wR8fR820nHT14Nums, 2048),
    (wR8fR820nHT15Labs, wR8fR820nHT15Nums, 2048), (wR8fR820nHT16Labs, wR8fR820nHT16Nums, 808)]
    [(wR8fR820nGT0Labs, wR8fR820nGT0Nums, 2048), (wR8fR820nGT1Labs, wR8fR820nGT1Nums, 2048),
    (wR8fR820nGT2Labs, wR8fR820nGT2Nums, 2048), (wR8fR820nGT3Labs, wR8fR820nGT3Nums, 2048),
    (wR8fR820nGT4Labs, wR8fR820nGT4Nums, 2048), (wR8fR820nGT5Labs, wR8fR820nGT5Nums, 2048),
    (wR8fR820nGT6Labs, wR8fR820nGT6Nums, 2048), (wR8fR820nGT7Labs, wR8fR820nGT7Nums, 2048),
    (wR8fR820nGT8Labs, wR8fR820nGT8Nums, 2048), (wR8fR820nGT9Labs, wR8fR820nGT9Nums, 2048),
    (wR8fR820nGT10Labs, wR8fR820nGT10Nums, 2048), (wR8fR820nGT11Labs, wR8fR820nGT11Nums, 2048),
    (wR8fR820nGT12Labs, wR8fR820nGT12Nums, 2048), (wR8fR820nGT13Labs, wR8fR820nGT13Nums, 2048),
    (wR8fR820nGT14Labs, wR8fR820nGT14Nums, 2048), (wR8fR820nGT15Labs, wR8fR820nGT15Nums, 2048),
    (wR8fR820nGT16Labs, wR8fR820nGT16Nums, 808)] 4358144 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wR8fR820n_Lsh : wR8fR820nL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR820nHT0Labs, wR8fR820nHT0Nums, 2048), (wR8fR820nHT1Labs, wR8fR820nHT1Nums, 2048),
    (wR8fR820nHT2Labs, wR8fR820nHT2Nums, 2048), (wR8fR820nHT3Labs, wR8fR820nHT3Nums, 2048),
    (wR8fR820nHT4Labs, wR8fR820nHT4Nums, 2048), (wR8fR820nHT5Labs, wR8fR820nHT5Nums, 2048),
    (wR8fR820nHT6Labs, wR8fR820nHT6Nums, 2048), (wR8fR820nHT7Labs, wR8fR820nHT7Nums, 2048),
    (wR8fR820nHT8Labs, wR8fR820nHT8Nums, 2048), (wR8fR820nHT9Labs, wR8fR820nHT9Nums, 2048),
    (wR8fR820nHT10Labs, wR8fR820nHT10Nums, 2048), (wR8fR820nHT11Labs, wR8fR820nHT11Nums, 2048),
    (wR8fR820nHT12Labs, wR8fR820nHT12Nums, 2048), (wR8fR820nHT13Labs, wR8fR820nHT13Nums, 2048),
    (wR8fR820nHT14Labs, wR8fR820nHT14Nums, 2048), (wR8fR820nHT15Labs, wR8fR820nHT15Nums, 2048),
    (wR8fR820nHT16Labs, wR8fR820nHT16Nums, 808)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wR8fR820n_Wsh : wR8fR820nW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR820nGT0Labs, wR8fR820nGT0Nums, 2048), (wR8fR820nGT1Labs, wR8fR820nGT1Nums, 2048),
    (wR8fR820nGT2Labs, wR8fR820nGT2Nums, 2048), (wR8fR820nGT3Labs, wR8fR820nGT3Nums, 2048),
    (wR8fR820nGT4Labs, wR8fR820nGT4Nums, 2048), (wR8fR820nGT5Labs, wR8fR820nGT5Nums, 2048),
    (wR8fR820nGT6Labs, wR8fR820nGT6Nums, 2048), (wR8fR820nGT7Labs, wR8fR820nGT7Nums, 2048),
    (wR8fR820nGT8Labs, wR8fR820nGT8Nums, 2048), (wR8fR820nGT9Labs, wR8fR820nGT9Nums, 2048),
    (wR8fR820nGT10Labs, wR8fR820nGT10Nums, 2048), (wR8fR820nGT11Labs, wR8fR820nGT11Nums, 2048),
    (wR8fR820nGT12Labs, wR8fR820nGT12Nums, 2048), (wR8fR820nGT13Labs, wR8fR820nGT13Nums, 2048),
    (wR8fR820nGT14Labs, wR8fR820nGT14Nums, 2048), (wR8fR820nGT15Labs, wR8fR820nGT15Nums, 2048),
    (wR8fR820nGT16Labs, wR8fR820nGT16Nums, 808)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wR8fR820n_hok : octPackOk 64 wR8fR820nL = true :=
  OctadDense.octPackOk_of_chk 64 6 false wR8fR820nL _ _ 4358144 wR8fR820n_Lsh wR8fR820n_chk

/-- The octad integer sum. -/
theorem wR8fR820n_octn : octSumZ 64 false wR8fR820nL wR8fR820nW = 4358144 :=
  OctadDense.octSumZ_of_chk 64 6 false wR8fR820nL wR8fR820nW _ _ 4358144 wR8fR820n_Lsh
      wR8fR820n_Wsh wR8fR820n_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wR8fR820n_selfchk : OctadDense.selfOctChk 64 [(wR8fR820nGT0Labs, wR8fR820nGT0Nums, 2048),
    (wR8fR820nGT1Labs, wR8fR820nGT1Nums, 2048), (wR8fR820nGT2Labs, wR8fR820nGT2Nums, 2048),
    (wR8fR820nGT3Labs, wR8fR820nGT3Nums, 2048), (wR8fR820nGT4Labs, wR8fR820nGT4Nums, 2048),
    (wR8fR820nGT5Labs, wR8fR820nGT5Nums, 2048), (wR8fR820nGT6Labs, wR8fR820nGT6Nums, 2048),
    (wR8fR820nGT7Labs, wR8fR820nGT7Nums, 2048), (wR8fR820nGT8Labs, wR8fR820nGT8Nums, 2048),
    (wR8fR820nGT9Labs, wR8fR820nGT9Nums, 2048), (wR8fR820nGT10Labs, wR8fR820nGT10Nums, 2048),
    (wR8fR820nGT11Labs, wR8fR820nGT11Nums, 2048), (wR8fR820nGT12Labs, wR8fR820nGT12Nums, 2048),
    (wR8fR820nGT13Labs, wR8fR820nGT13Nums, 2048), (wR8fR820nGT14Labs, wR8fR820nGT14Nums, 2048),
    (wR8fR820nGT15Labs, wR8fR820nGT15Nums, 2048), (wR8fR820nGT16Labs, wR8fR820nGT16Nums, 808)]
    544768 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wR8fR820n_hn : wR8fR820nL.sden * (octSumZ 64 false wR8fR820nL wR8fR820nW : ℚ) / 8 =
    wR8fR820nW.sden * (selfOctP wR8fR820nW : ℚ) := by
  rw [wR8fR820n_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wR8fR820nW _ 544768 wR8fR820n_Wsh
      wR8fR820n_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
