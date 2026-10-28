/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE4T26nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octads) of the identification Eighth[8]- <-> Tenth[40]+ (record
goctad:E4@T26-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGoctadE4T26n_chk : OctadDense.octSumChk 64 7 false [(wGoctadE4T26nHT0Labs,
    wGoctadE4T26nHT0Nums, 2048), (wGoctadE4T26nHT1Labs, wGoctadE4T26nHT1Nums, 2048),
    (wGoctadE4T26nHT2Labs, wGoctadE4T26nHT2Nums, 2048), (wGoctadE4T26nHT3Labs,
    wGoctadE4T26nHT3Nums, 2048), (wGoctadE4T26nHT4Labs, wGoctadE4T26nHT4Nums, 2048),
    (wGoctadE4T26nHT5Labs, wGoctadE4T26nHT5Nums, 2048), (wGoctadE4T26nHT6Labs,
    wGoctadE4T26nHT6Nums, 2048), (wGoctadE4T26nHT7Labs, wGoctadE4T26nHT7Nums, 2048),
    (wGoctadE4T26nHT8Labs, wGoctadE4T26nHT8Nums, 2048), (wGoctadE4T26nHT9Labs,
    wGoctadE4T26nHT9Nums, 2048), (wGoctadE4T26nHT10Labs, wGoctadE4T26nHT10Nums, 2048),
    (wGoctadE4T26nHT11Labs, wGoctadE4T26nHT11Nums, 2048), (wGoctadE4T26nHT12Labs,
    wGoctadE4T26nHT12Nums, 2048), (wGoctadE4T26nHT13Labs, wGoctadE4T26nHT13Nums, 2048),
    (wGoctadE4T26nHT14Labs, wGoctadE4T26nHT14Nums, 2048), (wGoctadE4T26nHT15Labs,
    wGoctadE4T26nHT15Nums, 2048), (wGoctadE4T26nHT16Labs, wGoctadE4T26nHT16Nums, 2048),
    (wGoctadE4T26nHT17Labs, wGoctadE4T26nHT17Nums, 2048), (wGoctadE4T26nHT18Labs,
    wGoctadE4T26nHT18Nums, 2048), (wGoctadE4T26nHT19Labs, wGoctadE4T26nHT19Nums, 2048),
    (wGoctadE4T26nHT20Labs, wGoctadE4T26nHT20Nums, 2048), (wGoctadE4T26nHT21Labs,
    wGoctadE4T26nHT21Nums, 668)] [(wGoctadE4T26nGT0Labs, wGoctadE4T26nGT0Nums, 2048),
    (wGoctadE4T26nGT1Labs, wGoctadE4T26nGT1Nums, 2048), (wGoctadE4T26nGT2Labs,
    wGoctadE4T26nGT2Nums, 2048), (wGoctadE4T26nGT3Labs, wGoctadE4T26nGT3Nums, 2048),
    (wGoctadE4T26nGT4Labs, wGoctadE4T26nGT4Nums, 2048), (wGoctadE4T26nGT5Labs,
    wGoctadE4T26nGT5Nums, 2048), (wGoctadE4T26nGT6Labs, wGoctadE4T26nGT6Nums, 2048),
    (wGoctadE4T26nGT7Labs, wGoctadE4T26nGT7Nums, 2048), (wGoctadE4T26nGT8Labs,
    wGoctadE4T26nGT8Nums, 2048), (wGoctadE4T26nGT9Labs, wGoctadE4T26nGT9Nums, 2048),
    (wGoctadE4T26nGT10Labs, wGoctadE4T26nGT10Nums, 2048), (wGoctadE4T26nGT11Labs,
    wGoctadE4T26nGT11Nums, 2048), (wGoctadE4T26nGT12Labs, wGoctadE4T26nGT12Nums, 2048),
    (wGoctadE4T26nGT13Labs, wGoctadE4T26nGT13Nums, 2048), (wGoctadE4T26nGT14Labs,
    wGoctadE4T26nGT14Nums, 2048), (wGoctadE4T26nGT15Labs, wGoctadE4T26nGT15Nums, 2048),
    (wGoctadE4T26nGT16Labs, wGoctadE4T26nGT16Nums, 2048), (wGoctadE4T26nGT17Labs,
    wGoctadE4T26nGT17Nums, 2048), (wGoctadE4T26nGT18Labs, wGoctadE4T26nGT18Nums, 2048),
    (wGoctadE4T26nGT19Labs, wGoctadE4T26nGT19Nums, 2048), (wGoctadE4T26nGT20Labs,
    wGoctadE4T26nGT20Nums, 2048), (wGoctadE4T26nGT21Labs, wGoctadE4T26nGT21Nums, 2048),
    (wGoctadE4T26nGT22Labs, wGoctadE4T26nGT22Nums, 1026)] 1015040 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGoctadE4T26n_Lsh : wGoctadE4T26nL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGoctadE4T26nHT0Labs, wGoctadE4T26nHT0Nums, 2048), (wGoctadE4T26nHT1Labs,
    wGoctadE4T26nHT1Nums, 2048), (wGoctadE4T26nHT2Labs, wGoctadE4T26nHT2Nums, 2048),
    (wGoctadE4T26nHT3Labs, wGoctadE4T26nHT3Nums, 2048), (wGoctadE4T26nHT4Labs,
    wGoctadE4T26nHT4Nums, 2048), (wGoctadE4T26nHT5Labs, wGoctadE4T26nHT5Nums, 2048),
    (wGoctadE4T26nHT6Labs, wGoctadE4T26nHT6Nums, 2048), (wGoctadE4T26nHT7Labs,
    wGoctadE4T26nHT7Nums, 2048), (wGoctadE4T26nHT8Labs, wGoctadE4T26nHT8Nums, 2048),
    (wGoctadE4T26nHT9Labs, wGoctadE4T26nHT9Nums, 2048), (wGoctadE4T26nHT10Labs,
    wGoctadE4T26nHT10Nums, 2048), (wGoctadE4T26nHT11Labs, wGoctadE4T26nHT11Nums, 2048),
    (wGoctadE4T26nHT12Labs, wGoctadE4T26nHT12Nums, 2048), (wGoctadE4T26nHT13Labs,
    wGoctadE4T26nHT13Nums, 2048), (wGoctadE4T26nHT14Labs, wGoctadE4T26nHT14Nums, 2048),
    (wGoctadE4T26nHT15Labs, wGoctadE4T26nHT15Nums, 2048), (wGoctadE4T26nHT16Labs,
    wGoctadE4T26nHT16Nums, 2048), (wGoctadE4T26nHT17Labs, wGoctadE4T26nHT17Nums, 2048),
    (wGoctadE4T26nHT18Labs, wGoctadE4T26nHT18Nums, 2048), (wGoctadE4T26nHT19Labs,
    wGoctadE4T26nHT19Nums, 2048), (wGoctadE4T26nHT20Labs, wGoctadE4T26nHT20Nums, 2048),
    (wGoctadE4T26nHT21Labs, wGoctadE4T26nHT21Nums, 668)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGoctadE4T26n_Wsh : wGoctadE4T26nW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGoctadE4T26nGT0Labs, wGoctadE4T26nGT0Nums, 2048), (wGoctadE4T26nGT1Labs,
    wGoctadE4T26nGT1Nums, 2048), (wGoctadE4T26nGT2Labs, wGoctadE4T26nGT2Nums, 2048),
    (wGoctadE4T26nGT3Labs, wGoctadE4T26nGT3Nums, 2048), (wGoctadE4T26nGT4Labs,
    wGoctadE4T26nGT4Nums, 2048), (wGoctadE4T26nGT5Labs, wGoctadE4T26nGT5Nums, 2048),
    (wGoctadE4T26nGT6Labs, wGoctadE4T26nGT6Nums, 2048), (wGoctadE4T26nGT7Labs,
    wGoctadE4T26nGT7Nums, 2048), (wGoctadE4T26nGT8Labs, wGoctadE4T26nGT8Nums, 2048),
    (wGoctadE4T26nGT9Labs, wGoctadE4T26nGT9Nums, 2048), (wGoctadE4T26nGT10Labs,
    wGoctadE4T26nGT10Nums, 2048), (wGoctadE4T26nGT11Labs, wGoctadE4T26nGT11Nums, 2048),
    (wGoctadE4T26nGT12Labs, wGoctadE4T26nGT12Nums, 2048), (wGoctadE4T26nGT13Labs,
    wGoctadE4T26nGT13Nums, 2048), (wGoctadE4T26nGT14Labs, wGoctadE4T26nGT14Nums, 2048),
    (wGoctadE4T26nGT15Labs, wGoctadE4T26nGT15Nums, 2048), (wGoctadE4T26nGT16Labs,
    wGoctadE4T26nGT16Nums, 2048), (wGoctadE4T26nGT17Labs, wGoctadE4T26nGT17Nums, 2048),
    (wGoctadE4T26nGT18Labs, wGoctadE4T26nGT18Nums, 2048), (wGoctadE4T26nGT19Labs,
    wGoctadE4T26nGT19Nums, 2048), (wGoctadE4T26nGT20Labs, wGoctadE4T26nGT20Nums, 2048),
    (wGoctadE4T26nGT21Labs, wGoctadE4T26nGT21Nums, 2048), (wGoctadE4T26nGT22Labs,
    wGoctadE4T26nGT22Nums, 1026)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGoctadE4T26n_hok : octPackOk 64 wGoctadE4T26nL = true :=
  OctadDense.octPackOk_of_chk 64 7 false wGoctadE4T26nL _ _ 1015040 wGoctadE4T26n_Lsh
      wGoctadE4T26n_chk

/-- The octad integer sum. -/
theorem wGoctadE4T26n_octn : octSumZ 64 false wGoctadE4T26nL wGoctadE4T26nW = 1015040 :=
  OctadDense.octSumZ_of_chk 64 7 false wGoctadE4T26nL wGoctadE4T26nW _ _ 1015040 wGoctadE4T26n_Lsh
      wGoctadE4T26n_Wsh wGoctadE4T26n_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGoctadE4T26n_selfchk : OctadDense.selfOctChk 64 [(wGoctadE4T26nGT0Labs,
    wGoctadE4T26nGT0Nums, 2048), (wGoctadE4T26nGT1Labs, wGoctadE4T26nGT1Nums, 2048),
    (wGoctadE4T26nGT2Labs, wGoctadE4T26nGT2Nums, 2048), (wGoctadE4T26nGT3Labs,
    wGoctadE4T26nGT3Nums, 2048), (wGoctadE4T26nGT4Labs, wGoctadE4T26nGT4Nums, 2048),
    (wGoctadE4T26nGT5Labs, wGoctadE4T26nGT5Nums, 2048), (wGoctadE4T26nGT6Labs,
    wGoctadE4T26nGT6Nums, 2048), (wGoctadE4T26nGT7Labs, wGoctadE4T26nGT7Nums, 2048),
    (wGoctadE4T26nGT8Labs, wGoctadE4T26nGT8Nums, 2048), (wGoctadE4T26nGT9Labs,
    wGoctadE4T26nGT9Nums, 2048), (wGoctadE4T26nGT10Labs, wGoctadE4T26nGT10Nums, 2048),
    (wGoctadE4T26nGT11Labs, wGoctadE4T26nGT11Nums, 2048), (wGoctadE4T26nGT12Labs,
    wGoctadE4T26nGT12Nums, 2048), (wGoctadE4T26nGT13Labs, wGoctadE4T26nGT13Nums, 2048),
    (wGoctadE4T26nGT14Labs, wGoctadE4T26nGT14Nums, 2048), (wGoctadE4T26nGT15Labs,
    wGoctadE4T26nGT15Nums, 2048), (wGoctadE4T26nGT16Labs, wGoctadE4T26nGT16Nums, 2048),
    (wGoctadE4T26nGT17Labs, wGoctadE4T26nGT17Nums, 2048), (wGoctadE4T26nGT18Labs,
    wGoctadE4T26nGT18Nums, 2048), (wGoctadE4T26nGT19Labs, wGoctadE4T26nGT19Nums, 2048),
    (wGoctadE4T26nGT20Labs, wGoctadE4T26nGT20Nums, 2048), (wGoctadE4T26nGT21Labs,
    wGoctadE4T26nGT21Nums, 2048), (wGoctadE4T26nGT22Labs, wGoctadE4T26nGT22Nums, 1026)] 507520 =
    true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGoctadE4T26n_hn : wGoctadE4T26nL.sden * (octSumZ 64 false wGoctadE4T26nL wGoctadE4T26nW :
    ℚ) / 8 =
    wGoctadE4T26nW.sden * (selfOctP wGoctadE4T26nW : ℚ) := by
  rw [wGoctadE4T26n_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGoctadE4T26nW _ 507520
      wGoctadE4T26n_Wsh wGoctadE4T26n_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
