/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c8nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT

/-! # Factory parts (octads) of the identification Eighth[13]+ <-> Seventh[14]- (record
gforest:S7c8-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGforestS7c8n_chk : OctadDense.octSumChk 64 5 false [(wGforestS7c8nHT0Labs,
    wGforestS7c8nHT0Nums, 2048), (wGforestS7c8nHT1Labs, wGforestS7c8nHT1Nums, 2048),
    (wGforestS7c8nHT2Labs, wGforestS7c8nHT2Nums, 2048), (wGforestS7c8nHT3Labs,
    wGforestS7c8nHT3Nums, 2048), (wGforestS7c8nHT4Labs, wGforestS7c8nHT4Nums, 2048),
    (wGforestS7c8nHT5Labs, wGforestS7c8nHT5Nums, 2048), (wGforestS7c8nHT6Labs,
    wGforestS7c8nHT6Nums, 2048), (wGforestS7c8nHT7Labs, wGforestS7c8nHT7Nums, 2048),
    (wGforestS7c8nHT8Labs, wGforestS7c8nHT8Nums, 2048), (wGforestS7c8nHT9Labs,
    wGforestS7c8nHT9Nums, 2048), (wGforestS7c8nHT10Labs, wGforestS7c8nHT10Nums, 2048),
    (wGforestS7c8nHT11Labs, wGforestS7c8nHT11Nums, 2048), (wGforestS7c8nHT12Labs,
    wGforestS7c8nHT12Nums, 2048), (wGforestS7c8nHT13Labs, wGforestS7c8nHT13Nums, 1000)]
    [(wGforestS7c8nGT0Labs, wGforestS7c8nGT0Nums, 2048), (wGforestS7c8nGT1Labs,
    wGforestS7c8nGT1Nums, 2048), (wGforestS7c8nGT2Labs, wGforestS7c8nGT2Nums, 2048),
    (wGforestS7c8nGT3Labs, wGforestS7c8nGT3Nums, 2048), (wGforestS7c8nGT4Labs,
    wGforestS7c8nGT4Nums, 2048), (wGforestS7c8nGT5Labs, wGforestS7c8nGT5Nums, 2048),
    (wGforestS7c8nGT6Labs, wGforestS7c8nGT6Nums, 2048), (wGforestS7c8nGT7Labs,
    wGforestS7c8nGT7Nums, 2048), (wGforestS7c8nGT8Labs, wGforestS7c8nGT8Nums, 2048),
    (wGforestS7c8nGT9Labs, wGforestS7c8nGT9Nums, 2048), (wGforestS7c8nGT10Labs,
    wGforestS7c8nGT10Nums, 2048), (wGforestS7c8nGT11Labs, wGforestS7c8nGT11Nums, 2048),
    (wGforestS7c8nGT12Labs, wGforestS7c8nGT12Nums, 2048), (wGforestS7c8nGT13Labs,
    wGforestS7c8nGT13Nums, 2048), (wGforestS7c8nGT14Labs, wGforestS7c8nGT14Nums, 2048),
    (wGforestS7c8nGT15Labs, wGforestS7c8nGT15Nums, 2048), (wGforestS7c8nGT16Labs,
    wGforestS7c8nGT16Nums, 2048), (wGforestS7c8nGT17Labs, wGforestS7c8nGT17Nums, 2048),
    (wGforestS7c8nGT18Labs, wGforestS7c8nGT18Nums, 2048), (wGforestS7c8nGT19Labs,
    wGforestS7c8nGT19Nums, 2048), (wGforestS7c8nGT20Labs, wGforestS7c8nGT20Nums, 2048),
    (wGforestS7c8nGT21Labs, wGforestS7c8nGT21Nums, 668)] 263392 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGforestS7c8n_Lsh : wGforestS7c8nL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGforestS7c8nHT0Labs, wGforestS7c8nHT0Nums, 2048), (wGforestS7c8nHT1Labs,
    wGforestS7c8nHT1Nums, 2048), (wGforestS7c8nHT2Labs, wGforestS7c8nHT2Nums, 2048),
    (wGforestS7c8nHT3Labs, wGforestS7c8nHT3Nums, 2048), (wGforestS7c8nHT4Labs,
    wGforestS7c8nHT4Nums, 2048), (wGforestS7c8nHT5Labs, wGforestS7c8nHT5Nums, 2048),
    (wGforestS7c8nHT6Labs, wGforestS7c8nHT6Nums, 2048), (wGforestS7c8nHT7Labs,
    wGforestS7c8nHT7Nums, 2048), (wGforestS7c8nHT8Labs, wGforestS7c8nHT8Nums, 2048),
    (wGforestS7c8nHT9Labs, wGforestS7c8nHT9Nums, 2048), (wGforestS7c8nHT10Labs,
    wGforestS7c8nHT10Nums, 2048), (wGforestS7c8nHT11Labs, wGforestS7c8nHT11Nums, 2048),
    (wGforestS7c8nHT12Labs, wGforestS7c8nHT12Nums, 2048), (wGforestS7c8nHT13Labs,
    wGforestS7c8nHT13Nums, 1000)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGforestS7c8n_Wsh : wGforestS7c8nW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGforestS7c8nGT0Labs, wGforestS7c8nGT0Nums, 2048), (wGforestS7c8nGT1Labs,
    wGforestS7c8nGT1Nums, 2048), (wGforestS7c8nGT2Labs, wGforestS7c8nGT2Nums, 2048),
    (wGforestS7c8nGT3Labs, wGforestS7c8nGT3Nums, 2048), (wGforestS7c8nGT4Labs,
    wGforestS7c8nGT4Nums, 2048), (wGforestS7c8nGT5Labs, wGforestS7c8nGT5Nums, 2048),
    (wGforestS7c8nGT6Labs, wGforestS7c8nGT6Nums, 2048), (wGforestS7c8nGT7Labs,
    wGforestS7c8nGT7Nums, 2048), (wGforestS7c8nGT8Labs, wGforestS7c8nGT8Nums, 2048),
    (wGforestS7c8nGT9Labs, wGforestS7c8nGT9Nums, 2048), (wGforestS7c8nGT10Labs,
    wGforestS7c8nGT10Nums, 2048), (wGforestS7c8nGT11Labs, wGforestS7c8nGT11Nums, 2048),
    (wGforestS7c8nGT12Labs, wGforestS7c8nGT12Nums, 2048), (wGforestS7c8nGT13Labs,
    wGforestS7c8nGT13Nums, 2048), (wGforestS7c8nGT14Labs, wGforestS7c8nGT14Nums, 2048),
    (wGforestS7c8nGT15Labs, wGforestS7c8nGT15Nums, 2048), (wGforestS7c8nGT16Labs,
    wGforestS7c8nGT16Nums, 2048), (wGforestS7c8nGT17Labs, wGforestS7c8nGT17Nums, 2048),
    (wGforestS7c8nGT18Labs, wGforestS7c8nGT18Nums, 2048), (wGforestS7c8nGT19Labs,
    wGforestS7c8nGT19Nums, 2048), (wGforestS7c8nGT20Labs, wGforestS7c8nGT20Nums, 2048),
    (wGforestS7c8nGT21Labs, wGforestS7c8nGT21Nums, 668)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGforestS7c8n_hok : octPackOk 64 wGforestS7c8nL = true :=
  OctadDense.octPackOk_of_chk 64 5 false wGforestS7c8nL _ _ 263392 wGforestS7c8n_Lsh
      wGforestS7c8n_chk

/-- The octad integer sum. -/
theorem wGforestS7c8n_octn : octSumZ 64 false wGforestS7c8nL wGforestS7c8nW = 263392 :=
  OctadDense.octSumZ_of_chk 64 5 false wGforestS7c8nL wGforestS7c8nW _ _ 263392 wGforestS7c8n_Lsh
      wGforestS7c8n_Wsh wGforestS7c8n_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGforestS7c8n_selfchk : OctadDense.selfOctChk 64 [(wGforestS7c8nGT0Labs,
    wGforestS7c8nGT0Nums, 2048), (wGforestS7c8nGT1Labs, wGforestS7c8nGT1Nums, 2048),
    (wGforestS7c8nGT2Labs, wGforestS7c8nGT2Nums, 2048), (wGforestS7c8nGT3Labs,
    wGforestS7c8nGT3Nums, 2048), (wGforestS7c8nGT4Labs, wGforestS7c8nGT4Nums, 2048),
    (wGforestS7c8nGT5Labs, wGforestS7c8nGT5Nums, 2048), (wGforestS7c8nGT6Labs,
    wGforestS7c8nGT6Nums, 2048), (wGforestS7c8nGT7Labs, wGforestS7c8nGT7Nums, 2048),
    (wGforestS7c8nGT8Labs, wGforestS7c8nGT8Nums, 2048), (wGforestS7c8nGT9Labs,
    wGforestS7c8nGT9Nums, 2048), (wGforestS7c8nGT10Labs, wGforestS7c8nGT10Nums, 2048),
    (wGforestS7c8nGT11Labs, wGforestS7c8nGT11Nums, 2048), (wGforestS7c8nGT12Labs,
    wGforestS7c8nGT12Nums, 2048), (wGforestS7c8nGT13Labs, wGforestS7c8nGT13Nums, 2048),
    (wGforestS7c8nGT14Labs, wGforestS7c8nGT14Nums, 2048), (wGforestS7c8nGT15Labs,
    wGforestS7c8nGT15Nums, 2048), (wGforestS7c8nGT16Labs, wGforestS7c8nGT16Nums, 2048),
    (wGforestS7c8nGT17Labs, wGforestS7c8nGT17Nums, 2048), (wGforestS7c8nGT18Labs,
    wGforestS7c8nGT18Nums, 2048), (wGforestS7c8nGT19Labs, wGforestS7c8nGT19Nums, 2048),
    (wGforestS7c8nGT20Labs, wGforestS7c8nGT20Nums, 2048), (wGforestS7c8nGT21Labs,
    wGforestS7c8nGT21Nums, 668)] 32924 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGforestS7c8n_hn : wGforestS7c8nL.sden * (octSumZ 64 false wGforestS7c8nL wGforestS7c8nW :
    ℚ) / 8 =
    wGforestS7c8nW.sden * (selfOctP wGforestS7c8nW : ℚ) := by
  rw [wGforestS7c8n_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGforestS7c8nW _ 32924
      wGforestS7c8n_Wsh wGforestS7c8n_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
