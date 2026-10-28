/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE10T27nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octads) of the identification Eighth[14]- <-> Tenth[55]- (record
goctad:E10@T27-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGoctadE10T27n_chk : OctadDense.octSumChk 64 7 false [(wGoctadE10T27nHT0Labs,
    wGoctadE10T27nHT0Nums, 2048), (wGoctadE10T27nHT1Labs, wGoctadE10T27nHT1Nums, 2048),
    (wGoctadE10T27nHT2Labs, wGoctadE10T27nHT2Nums, 2048), (wGoctadE10T27nHT3Labs,
    wGoctadE10T27nHT3Nums, 2048), (wGoctadE10T27nHT4Labs, wGoctadE10T27nHT4Nums, 2048),
    (wGoctadE10T27nHT5Labs, wGoctadE10T27nHT5Nums, 2048), (wGoctadE10T27nHT6Labs,
    wGoctadE10T27nHT6Nums, 2048), (wGoctadE10T27nHT7Labs, wGoctadE10T27nHT7Nums, 2048),
    (wGoctadE10T27nHT8Labs, wGoctadE10T27nHT8Nums, 2048), (wGoctadE10T27nHT9Labs,
    wGoctadE10T27nHT9Nums, 2048), (wGoctadE10T27nHT10Labs, wGoctadE10T27nHT10Nums, 2048),
    (wGoctadE10T27nHT11Labs, wGoctadE10T27nHT11Nums, 2048), (wGoctadE10T27nHT12Labs,
    wGoctadE10T27nHT12Nums, 2048), (wGoctadE10T27nHT13Labs, wGoctadE10T27nHT13Nums, 2048),
    (wGoctadE10T27nHT14Labs, wGoctadE10T27nHT14Nums, 2048), (wGoctadE10T27nHT15Labs,
    wGoctadE10T27nHT15Nums, 2048), (wGoctadE10T27nHT16Labs, wGoctadE10T27nHT16Nums, 2048),
    (wGoctadE10T27nHT17Labs, wGoctadE10T27nHT17Nums, 2048), (wGoctadE10T27nHT18Labs,
    wGoctadE10T27nHT18Nums, 2048), (wGoctadE10T27nHT19Labs, wGoctadE10T27nHT19Nums, 2048),
    (wGoctadE10T27nHT20Labs, wGoctadE10T27nHT20Nums, 2048), (wGoctadE10T27nHT21Labs,
    wGoctadE10T27nHT21Nums, 668)] [(wGoctadE10T27nGT0Labs, wGoctadE10T27nGT0Nums, 2048),
    (wGoctadE10T27nGT1Labs, wGoctadE10T27nGT1Nums, 2048), (wGoctadE10T27nGT2Labs,
    wGoctadE10T27nGT2Nums, 2048), (wGoctadE10T27nGT3Labs, wGoctadE10T27nGT3Nums, 2048),
    (wGoctadE10T27nGT4Labs, wGoctadE10T27nGT4Nums, 2048), (wGoctadE10T27nGT5Labs,
    wGoctadE10T27nGT5Nums, 2048), (wGoctadE10T27nGT6Labs, wGoctadE10T27nGT6Nums, 2048),
    (wGoctadE10T27nGT7Labs, wGoctadE10T27nGT7Nums, 2048), (wGoctadE10T27nGT8Labs,
    wGoctadE10T27nGT8Nums, 2048), (wGoctadE10T27nGT9Labs, wGoctadE10T27nGT9Nums, 2048),
    (wGoctadE10T27nGT10Labs, wGoctadE10T27nGT10Nums, 2048), (wGoctadE10T27nGT11Labs,
    wGoctadE10T27nGT11Nums, 2048), (wGoctadE10T27nGT12Labs, wGoctadE10T27nGT12Nums, 2048),
    (wGoctadE10T27nGT13Labs, wGoctadE10T27nGT13Nums, 2048), (wGoctadE10T27nGT14Labs,
    wGoctadE10T27nGT14Nums, 2048), (wGoctadE10T27nGT15Labs, wGoctadE10T27nGT15Nums, 2048),
    (wGoctadE10T27nGT16Labs, wGoctadE10T27nGT16Nums, 2048), (wGoctadE10T27nGT17Labs,
    wGoctadE10T27nGT17Nums, 2048), (wGoctadE10T27nGT18Labs, wGoctadE10T27nGT18Nums, 2048),
    (wGoctadE10T27nGT19Labs, wGoctadE10T27nGT19Nums, 2048), (wGoctadE10T27nGT20Labs,
    wGoctadE10T27nGT20Nums, 2048), (wGoctadE10T27nGT21Labs, wGoctadE10T27nGT21Nums, 2048),
    (wGoctadE10T27nGT22Labs, wGoctadE10T27nGT22Nums, 1026)] 1014784 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGoctadE10T27n_Lsh : wGoctadE10T27nL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGoctadE10T27nHT0Labs, wGoctadE10T27nHT0Nums, 2048), (wGoctadE10T27nHT1Labs,
    wGoctadE10T27nHT1Nums, 2048), (wGoctadE10T27nHT2Labs, wGoctadE10T27nHT2Nums, 2048),
    (wGoctadE10T27nHT3Labs, wGoctadE10T27nHT3Nums, 2048), (wGoctadE10T27nHT4Labs,
    wGoctadE10T27nHT4Nums, 2048), (wGoctadE10T27nHT5Labs, wGoctadE10T27nHT5Nums, 2048),
    (wGoctadE10T27nHT6Labs, wGoctadE10T27nHT6Nums, 2048), (wGoctadE10T27nHT7Labs,
    wGoctadE10T27nHT7Nums, 2048), (wGoctadE10T27nHT8Labs, wGoctadE10T27nHT8Nums, 2048),
    (wGoctadE10T27nHT9Labs, wGoctadE10T27nHT9Nums, 2048), (wGoctadE10T27nHT10Labs,
    wGoctadE10T27nHT10Nums, 2048), (wGoctadE10T27nHT11Labs, wGoctadE10T27nHT11Nums, 2048),
    (wGoctadE10T27nHT12Labs, wGoctadE10T27nHT12Nums, 2048), (wGoctadE10T27nHT13Labs,
    wGoctadE10T27nHT13Nums, 2048), (wGoctadE10T27nHT14Labs, wGoctadE10T27nHT14Nums, 2048),
    (wGoctadE10T27nHT15Labs, wGoctadE10T27nHT15Nums, 2048), (wGoctadE10T27nHT16Labs,
    wGoctadE10T27nHT16Nums, 2048), (wGoctadE10T27nHT17Labs, wGoctadE10T27nHT17Nums, 2048),
    (wGoctadE10T27nHT18Labs, wGoctadE10T27nHT18Nums, 2048), (wGoctadE10T27nHT19Labs,
    wGoctadE10T27nHT19Nums, 2048), (wGoctadE10T27nHT20Labs, wGoctadE10T27nHT20Nums, 2048),
    (wGoctadE10T27nHT21Labs, wGoctadE10T27nHT21Nums, 668)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGoctadE10T27n_Wsh : wGoctadE10T27nW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGoctadE10T27nGT0Labs, wGoctadE10T27nGT0Nums, 2048), (wGoctadE10T27nGT1Labs,
    wGoctadE10T27nGT1Nums, 2048), (wGoctadE10T27nGT2Labs, wGoctadE10T27nGT2Nums, 2048),
    (wGoctadE10T27nGT3Labs, wGoctadE10T27nGT3Nums, 2048), (wGoctadE10T27nGT4Labs,
    wGoctadE10T27nGT4Nums, 2048), (wGoctadE10T27nGT5Labs, wGoctadE10T27nGT5Nums, 2048),
    (wGoctadE10T27nGT6Labs, wGoctadE10T27nGT6Nums, 2048), (wGoctadE10T27nGT7Labs,
    wGoctadE10T27nGT7Nums, 2048), (wGoctadE10T27nGT8Labs, wGoctadE10T27nGT8Nums, 2048),
    (wGoctadE10T27nGT9Labs, wGoctadE10T27nGT9Nums, 2048), (wGoctadE10T27nGT10Labs,
    wGoctadE10T27nGT10Nums, 2048), (wGoctadE10T27nGT11Labs, wGoctadE10T27nGT11Nums, 2048),
    (wGoctadE10T27nGT12Labs, wGoctadE10T27nGT12Nums, 2048), (wGoctadE10T27nGT13Labs,
    wGoctadE10T27nGT13Nums, 2048), (wGoctadE10T27nGT14Labs, wGoctadE10T27nGT14Nums, 2048),
    (wGoctadE10T27nGT15Labs, wGoctadE10T27nGT15Nums, 2048), (wGoctadE10T27nGT16Labs,
    wGoctadE10T27nGT16Nums, 2048), (wGoctadE10T27nGT17Labs, wGoctadE10T27nGT17Nums, 2048),
    (wGoctadE10T27nGT18Labs, wGoctadE10T27nGT18Nums, 2048), (wGoctadE10T27nGT19Labs,
    wGoctadE10T27nGT19Nums, 2048), (wGoctadE10T27nGT20Labs, wGoctadE10T27nGT20Nums, 2048),
    (wGoctadE10T27nGT21Labs, wGoctadE10T27nGT21Nums, 2048), (wGoctadE10T27nGT22Labs,
    wGoctadE10T27nGT22Nums, 1026)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGoctadE10T27n_hok : octPackOk 64 wGoctadE10T27nL = true :=
  OctadDense.octPackOk_of_chk 64 7 false wGoctadE10T27nL _ _ 1014784 wGoctadE10T27n_Lsh
      wGoctadE10T27n_chk

/-- The octad integer sum. -/
theorem wGoctadE10T27n_octn : octSumZ 64 false wGoctadE10T27nL wGoctadE10T27nW = 1014784 :=
  OctadDense.octSumZ_of_chk 64 7 false wGoctadE10T27nL wGoctadE10T27nW _ _ 1014784
      wGoctadE10T27n_Lsh wGoctadE10T27n_Wsh wGoctadE10T27n_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGoctadE10T27n_selfchk : OctadDense.selfOctChk 64 [(wGoctadE10T27nGT0Labs,
    wGoctadE10T27nGT0Nums, 2048), (wGoctadE10T27nGT1Labs, wGoctadE10T27nGT1Nums, 2048),
    (wGoctadE10T27nGT2Labs, wGoctadE10T27nGT2Nums, 2048), (wGoctadE10T27nGT3Labs,
    wGoctadE10T27nGT3Nums, 2048), (wGoctadE10T27nGT4Labs, wGoctadE10T27nGT4Nums, 2048),
    (wGoctadE10T27nGT5Labs, wGoctadE10T27nGT5Nums, 2048), (wGoctadE10T27nGT6Labs,
    wGoctadE10T27nGT6Nums, 2048), (wGoctadE10T27nGT7Labs, wGoctadE10T27nGT7Nums, 2048),
    (wGoctadE10T27nGT8Labs, wGoctadE10T27nGT8Nums, 2048), (wGoctadE10T27nGT9Labs,
    wGoctadE10T27nGT9Nums, 2048), (wGoctadE10T27nGT10Labs, wGoctadE10T27nGT10Nums, 2048),
    (wGoctadE10T27nGT11Labs, wGoctadE10T27nGT11Nums, 2048), (wGoctadE10T27nGT12Labs,
    wGoctadE10T27nGT12Nums, 2048), (wGoctadE10T27nGT13Labs, wGoctadE10T27nGT13Nums, 2048),
    (wGoctadE10T27nGT14Labs, wGoctadE10T27nGT14Nums, 2048), (wGoctadE10T27nGT15Labs,
    wGoctadE10T27nGT15Nums, 2048), (wGoctadE10T27nGT16Labs, wGoctadE10T27nGT16Nums, 2048),
    (wGoctadE10T27nGT17Labs, wGoctadE10T27nGT17Nums, 2048), (wGoctadE10T27nGT18Labs,
    wGoctadE10T27nGT18Nums, 2048), (wGoctadE10T27nGT19Labs, wGoctadE10T27nGT19Nums, 2048),
    (wGoctadE10T27nGT20Labs, wGoctadE10T27nGT20Nums, 2048), (wGoctadE10T27nGT21Labs,
    wGoctadE10T27nGT21Nums, 2048), (wGoctadE10T27nGT22Labs, wGoctadE10T27nGT22Nums, 1026)] 507392
    = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGoctadE10T27n_hn : wGoctadE10T27nL.sden * (octSumZ 64 false wGoctadE10T27nL
    wGoctadE10T27nW : ℚ) / 8 =
    wGoctadE10T27nW.sden * (selfOctP wGoctadE10T27nW : ℚ) := by
  rw [wGoctadE10T27n_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGoctadE10T27nW _ 507392
      wGoctadE10T27n_Wsh wGoctadE10T27n_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
