/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE34T21nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octads) of the identification Eighth[47]- <-> Tenth[26]+ (record
goctad:E34@T21-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem wGoctadE34T21n_chk : OctadDense.octSumChk 64 7 false [(wGoctadE34T21nHT0Labs,
    wGoctadE34T21nHT0Nums, 2048), (wGoctadE34T21nHT1Labs, wGoctadE34T21nHT1Nums, 2048),
    (wGoctadE34T21nHT2Labs, wGoctadE34T21nHT2Nums, 2048), (wGoctadE34T21nHT3Labs,
    wGoctadE34T21nHT3Nums, 2048), (wGoctadE34T21nHT4Labs, wGoctadE34T21nHT4Nums, 2048),
    (wGoctadE34T21nHT5Labs, wGoctadE34T21nHT5Nums, 2048), (wGoctadE34T21nHT6Labs,
    wGoctadE34T21nHT6Nums, 2048), (wGoctadE34T21nHT7Labs, wGoctadE34T21nHT7Nums, 2048),
    (wGoctadE34T21nHT8Labs, wGoctadE34T21nHT8Nums, 2048), (wGoctadE34T21nHT9Labs,
    wGoctadE34T21nHT9Nums, 2048), (wGoctadE34T21nHT10Labs, wGoctadE34T21nHT10Nums, 2048),
    (wGoctadE34T21nHT11Labs, wGoctadE34T21nHT11Nums, 2048), (wGoctadE34T21nHT12Labs,
    wGoctadE34T21nHT12Nums, 2048), (wGoctadE34T21nHT13Labs, wGoctadE34T21nHT13Nums, 2048),
    (wGoctadE34T21nHT14Labs, wGoctadE34T21nHT14Nums, 2048), (wGoctadE34T21nHT15Labs,
    wGoctadE34T21nHT15Nums, 2048), (wGoctadE34T21nHT16Labs, wGoctadE34T21nHT16Nums, 2048),
    (wGoctadE34T21nHT17Labs, wGoctadE34T21nHT17Nums, 2048), (wGoctadE34T21nHT18Labs,
    wGoctadE34T21nHT18Nums, 2048), (wGoctadE34T21nHT19Labs, wGoctadE34T21nHT19Nums, 2048),
    (wGoctadE34T21nHT20Labs, wGoctadE34T21nHT20Nums, 2048), (wGoctadE34T21nHT21Labs,
    wGoctadE34T21nHT21Nums, 668)] [(wGoctadE34T21nGT0Labs, wGoctadE34T21nGT0Nums, 2048),
    (wGoctadE34T21nGT1Labs, wGoctadE34T21nGT1Nums, 2048), (wGoctadE34T21nGT2Labs,
    wGoctadE34T21nGT2Nums, 2048), (wGoctadE34T21nGT3Labs, wGoctadE34T21nGT3Nums, 2048),
    (wGoctadE34T21nGT4Labs, wGoctadE34T21nGT4Nums, 2048), (wGoctadE34T21nGT5Labs,
    wGoctadE34T21nGT5Nums, 2048), (wGoctadE34T21nGT6Labs, wGoctadE34T21nGT6Nums, 2048),
    (wGoctadE34T21nGT7Labs, wGoctadE34T21nGT7Nums, 2048), (wGoctadE34T21nGT8Labs,
    wGoctadE34T21nGT8Nums, 2048), (wGoctadE34T21nGT9Labs, wGoctadE34T21nGT9Nums, 2048),
    (wGoctadE34T21nGT10Labs, wGoctadE34T21nGT10Nums, 2048), (wGoctadE34T21nGT11Labs,
    wGoctadE34T21nGT11Nums, 2048), (wGoctadE34T21nGT12Labs, wGoctadE34T21nGT12Nums, 2048),
    (wGoctadE34T21nGT13Labs, wGoctadE34T21nGT13Nums, 2048), (wGoctadE34T21nGT14Labs,
    wGoctadE34T21nGT14Nums, 2048), (wGoctadE34T21nGT15Labs, wGoctadE34T21nGT15Nums, 2048),
    (wGoctadE34T21nGT16Labs, wGoctadE34T21nGT16Nums, 2048), (wGoctadE34T21nGT17Labs,
    wGoctadE34T21nGT17Nums, 2048), (wGoctadE34T21nGT18Labs, wGoctadE34T21nGT18Nums, 2048),
    (wGoctadE34T21nGT19Labs, wGoctadE34T21nGT19Nums, 2048), (wGoctadE34T21nGT20Labs,
    wGoctadE34T21nGT20Nums, 2048), (wGoctadE34T21nGT21Labs, wGoctadE34T21nGT21Nums, 2048),
    (wGoctadE34T21nGT22Labs, wGoctadE34T21nGT22Nums, 1026)] 1015040 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem wGoctadE34T21n_Lsh : wGoctadE34T21nL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGoctadE34T21nHT0Labs, wGoctadE34T21nHT0Nums, 2048), (wGoctadE34T21nHT1Labs,
    wGoctadE34T21nHT1Nums, 2048), (wGoctadE34T21nHT2Labs, wGoctadE34T21nHT2Nums, 2048),
    (wGoctadE34T21nHT3Labs, wGoctadE34T21nHT3Nums, 2048), (wGoctadE34T21nHT4Labs,
    wGoctadE34T21nHT4Nums, 2048), (wGoctadE34T21nHT5Labs, wGoctadE34T21nHT5Nums, 2048),
    (wGoctadE34T21nHT6Labs, wGoctadE34T21nHT6Nums, 2048), (wGoctadE34T21nHT7Labs,
    wGoctadE34T21nHT7Nums, 2048), (wGoctadE34T21nHT8Labs, wGoctadE34T21nHT8Nums, 2048),
    (wGoctadE34T21nHT9Labs, wGoctadE34T21nHT9Nums, 2048), (wGoctadE34T21nHT10Labs,
    wGoctadE34T21nHT10Nums, 2048), (wGoctadE34T21nHT11Labs, wGoctadE34T21nHT11Nums, 2048),
    (wGoctadE34T21nHT12Labs, wGoctadE34T21nHT12Nums, 2048), (wGoctadE34T21nHT13Labs,
    wGoctadE34T21nHT13Nums, 2048), (wGoctadE34T21nHT14Labs, wGoctadE34T21nHT14Nums, 2048),
    (wGoctadE34T21nHT15Labs, wGoctadE34T21nHT15Nums, 2048), (wGoctadE34T21nHT16Labs,
    wGoctadE34T21nHT16Nums, 2048), (wGoctadE34T21nHT17Labs, wGoctadE34T21nHT17Nums, 2048),
    (wGoctadE34T21nHT18Labs, wGoctadE34T21nHT18Nums, 2048), (wGoctadE34T21nHT19Labs,
    wGoctadE34T21nHT19Nums, 2048), (wGoctadE34T21nHT20Labs, wGoctadE34T21nHT20Nums, 2048),
    (wGoctadE34T21nHT21Labs, wGoctadE34T21nHT21Nums, 668)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem wGoctadE34T21n_Wsh : wGoctadE34T21nW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGoctadE34T21nGT0Labs, wGoctadE34T21nGT0Nums, 2048), (wGoctadE34T21nGT1Labs,
    wGoctadE34T21nGT1Nums, 2048), (wGoctadE34T21nGT2Labs, wGoctadE34T21nGT2Nums, 2048),
    (wGoctadE34T21nGT3Labs, wGoctadE34T21nGT3Nums, 2048), (wGoctadE34T21nGT4Labs,
    wGoctadE34T21nGT4Nums, 2048), (wGoctadE34T21nGT5Labs, wGoctadE34T21nGT5Nums, 2048),
    (wGoctadE34T21nGT6Labs, wGoctadE34T21nGT6Nums, 2048), (wGoctadE34T21nGT7Labs,
    wGoctadE34T21nGT7Nums, 2048), (wGoctadE34T21nGT8Labs, wGoctadE34T21nGT8Nums, 2048),
    (wGoctadE34T21nGT9Labs, wGoctadE34T21nGT9Nums, 2048), (wGoctadE34T21nGT10Labs,
    wGoctadE34T21nGT10Nums, 2048), (wGoctadE34T21nGT11Labs, wGoctadE34T21nGT11Nums, 2048),
    (wGoctadE34T21nGT12Labs, wGoctadE34T21nGT12Nums, 2048), (wGoctadE34T21nGT13Labs,
    wGoctadE34T21nGT13Nums, 2048), (wGoctadE34T21nGT14Labs, wGoctadE34T21nGT14Nums, 2048),
    (wGoctadE34T21nGT15Labs, wGoctadE34T21nGT15Nums, 2048), (wGoctadE34T21nGT16Labs,
    wGoctadE34T21nGT16Nums, 2048), (wGoctadE34T21nGT17Labs, wGoctadE34T21nGT17Nums, 2048),
    (wGoctadE34T21nGT18Labs, wGoctadE34T21nGT18Nums, 2048), (wGoctadE34T21nGT19Labs,
    wGoctadE34T21nGT19Nums, 2048), (wGoctadE34T21nGT20Labs, wGoctadE34T21nGT20Nums, 2048),
    (wGoctadE34T21nGT21Labs, wGoctadE34T21nGT21Nums, 2048), (wGoctadE34T21nGT22Labs,
    wGoctadE34T21nGT22Nums, 1026)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem wGoctadE34T21n_hok : octPackOk 64 wGoctadE34T21nL = true :=
  OctadDense.octPackOk_of_chk 64 7 false wGoctadE34T21nL _ _ 1015040 wGoctadE34T21n_Lsh
      wGoctadE34T21n_chk

/-- The octad integer sum. -/
theorem wGoctadE34T21n_octn : octSumZ 64 false wGoctadE34T21nL wGoctadE34T21nW = 1015040 :=
  OctadDense.octSumZ_of_chk 64 7 false wGoctadE34T21nL wGoctadE34T21nW _ _ 1015040
      wGoctadE34T21n_Lsh wGoctadE34T21n_Wsh wGoctadE34T21n_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem wGoctadE34T21n_selfchk : OctadDense.selfOctChk 64 [(wGoctadE34T21nGT0Labs,
    wGoctadE34T21nGT0Nums, 2048), (wGoctadE34T21nGT1Labs, wGoctadE34T21nGT1Nums, 2048),
    (wGoctadE34T21nGT2Labs, wGoctadE34T21nGT2Nums, 2048), (wGoctadE34T21nGT3Labs,
    wGoctadE34T21nGT3Nums, 2048), (wGoctadE34T21nGT4Labs, wGoctadE34T21nGT4Nums, 2048),
    (wGoctadE34T21nGT5Labs, wGoctadE34T21nGT5Nums, 2048), (wGoctadE34T21nGT6Labs,
    wGoctadE34T21nGT6Nums, 2048), (wGoctadE34T21nGT7Labs, wGoctadE34T21nGT7Nums, 2048),
    (wGoctadE34T21nGT8Labs, wGoctadE34T21nGT8Nums, 2048), (wGoctadE34T21nGT9Labs,
    wGoctadE34T21nGT9Nums, 2048), (wGoctadE34T21nGT10Labs, wGoctadE34T21nGT10Nums, 2048),
    (wGoctadE34T21nGT11Labs, wGoctadE34T21nGT11Nums, 2048), (wGoctadE34T21nGT12Labs,
    wGoctadE34T21nGT12Nums, 2048), (wGoctadE34T21nGT13Labs, wGoctadE34T21nGT13Nums, 2048),
    (wGoctadE34T21nGT14Labs, wGoctadE34T21nGT14Nums, 2048), (wGoctadE34T21nGT15Labs,
    wGoctadE34T21nGT15Nums, 2048), (wGoctadE34T21nGT16Labs, wGoctadE34T21nGT16Nums, 2048),
    (wGoctadE34T21nGT17Labs, wGoctadE34T21nGT17Nums, 2048), (wGoctadE34T21nGT18Labs,
    wGoctadE34T21nGT18Nums, 2048), (wGoctadE34T21nGT19Labs, wGoctadE34T21nGT19Nums, 2048),
    (wGoctadE34T21nGT20Labs, wGoctadE34T21nGT20Nums, 2048), (wGoctadE34T21nGT21Labs,
    wGoctadE34T21nGT21Nums, 2048), (wGoctadE34T21nGT22Labs, wGoctadE34T21nGT22Nums, 1026)] 507520
    = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem wGoctadE34T21n_hn : wGoctadE34T21nL.sden * (octSumZ 64 false wGoctadE34T21nL
    wGoctadE34T21nW : ℚ) / 8 =
    wGoctadE34T21nW.sden * (selfOctP wGoctadE34T21nW : ℚ) := by
  rw [wGoctadE34T21n_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 wGoctadE34T21nW _ 507520
      wGoctadE34T21n_Wsh wGoctadE34T21n_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
