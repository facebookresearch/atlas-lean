/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW1nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (octads) of the identification Twelfth[1]- <-> Twelfth[1]+ (record
gtwelfth:W1-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem twGtwelfthW1n_chk : OctadDense.octSumChk 64 5 false [(twGtwelfthW1nHT0Labs,
    twGtwelfthW1nHT0Nums, 2048), (twGtwelfthW1nHT1Labs, twGtwelfthW1nHT1Nums, 2048),
    (twGtwelfthW1nHT2Labs, twGtwelfthW1nHT2Nums, 2048), (twGtwelfthW1nHT3Labs,
    twGtwelfthW1nHT3Nums, 2048), (twGtwelfthW1nHT4Labs, twGtwelfthW1nHT4Nums, 2048),
    (twGtwelfthW1nHT5Labs, twGtwelfthW1nHT5Nums, 2048), (twGtwelfthW1nHT6Labs,
    twGtwelfthW1nHT6Nums, 2048), (twGtwelfthW1nHT7Labs, twGtwelfthW1nHT7Nums, 2048),
    (twGtwelfthW1nHT8Labs, twGtwelfthW1nHT8Nums, 2048), (twGtwelfthW1nHT9Labs,
    twGtwelfthW1nHT9Nums, 2048), (twGtwelfthW1nHT10Labs, twGtwelfthW1nHT10Nums, 2048),
    (twGtwelfthW1nHT11Labs, twGtwelfthW1nHT11Nums, 2048), (twGtwelfthW1nHT12Labs,
    twGtwelfthW1nHT12Nums, 2048), (twGtwelfthW1nHT13Labs, twGtwelfthW1nHT13Nums, 2048),
    (twGtwelfthW1nHT14Labs, twGtwelfthW1nHT14Nums, 2048), (twGtwelfthW1nHT15Labs,
    twGtwelfthW1nHT15Nums, 2048), (twGtwelfthW1nHT16Labs, twGtwelfthW1nHT16Nums, 2048),
    (twGtwelfthW1nHT17Labs, twGtwelfthW1nHT17Nums, 2048), (twGtwelfthW1nHT18Labs,
    twGtwelfthW1nHT18Nums, 2048), (twGtwelfthW1nHT19Labs, twGtwelfthW1nHT19Nums, 2048),
    (twGtwelfthW1nHT20Labs, twGtwelfthW1nHT20Nums, 2048), (twGtwelfthW1nHT21Labs,
    twGtwelfthW1nHT21Nums, 2048), (twGtwelfthW1nHT22Labs, twGtwelfthW1nHT22Nums, 1704)]
    [(twGtwelfthW1nGT0Labs, twGtwelfthW1nGT0Nums, 2048), (twGtwelfthW1nGT1Labs,
    twGtwelfthW1nGT1Nums, 2048), (twGtwelfthW1nGT2Labs, twGtwelfthW1nGT2Nums, 2048),
    (twGtwelfthW1nGT3Labs, twGtwelfthW1nGT3Nums, 2048), (twGtwelfthW1nGT4Labs,
    twGtwelfthW1nGT4Nums, 2048), (twGtwelfthW1nGT5Labs, twGtwelfthW1nGT5Nums, 2048),
    (twGtwelfthW1nGT6Labs, twGtwelfthW1nGT6Nums, 2048), (twGtwelfthW1nGT7Labs,
    twGtwelfthW1nGT7Nums, 2048), (twGtwelfthW1nGT8Labs, twGtwelfthW1nGT8Nums, 2048),
    (twGtwelfthW1nGT9Labs, twGtwelfthW1nGT9Nums, 2048), (twGtwelfthW1nGT10Labs,
    twGtwelfthW1nGT10Nums, 2048), (twGtwelfthW1nGT11Labs, twGtwelfthW1nGT11Nums, 2048),
    (twGtwelfthW1nGT12Labs, twGtwelfthW1nGT12Nums, 2048), (twGtwelfthW1nGT13Labs,
    twGtwelfthW1nGT13Nums, 2048), (twGtwelfthW1nGT14Labs, twGtwelfthW1nGT14Nums, 2048),
    (twGtwelfthW1nGT15Labs, twGtwelfthW1nGT15Nums, 2048), (twGtwelfthW1nGT16Labs,
    twGtwelfthW1nGT16Nums, 2048), (twGtwelfthW1nGT17Labs, twGtwelfthW1nGT17Nums, 2048),
    (twGtwelfthW1nGT18Labs, twGtwelfthW1nGT18Nums, 2048), (twGtwelfthW1nGT19Labs,
    twGtwelfthW1nGT19Nums, 2048), (twGtwelfthW1nGT20Labs, twGtwelfthW1nGT20Nums, 2048),
    (twGtwelfthW1nGT21Labs, twGtwelfthW1nGT21Nums, 2048), (twGtwelfthW1nGT22Labs,
    twGtwelfthW1nGT22Nums, 1704)] 4073472 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem twGtwelfthW1n_Lsh : twGtwelfthW1nL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(twGtwelfthW1nHT0Labs, twGtwelfthW1nHT0Nums, 2048), (twGtwelfthW1nHT1Labs,
    twGtwelfthW1nHT1Nums, 2048), (twGtwelfthW1nHT2Labs, twGtwelfthW1nHT2Nums, 2048),
    (twGtwelfthW1nHT3Labs, twGtwelfthW1nHT3Nums, 2048), (twGtwelfthW1nHT4Labs,
    twGtwelfthW1nHT4Nums, 2048), (twGtwelfthW1nHT5Labs, twGtwelfthW1nHT5Nums, 2048),
    (twGtwelfthW1nHT6Labs, twGtwelfthW1nHT6Nums, 2048), (twGtwelfthW1nHT7Labs,
    twGtwelfthW1nHT7Nums, 2048), (twGtwelfthW1nHT8Labs, twGtwelfthW1nHT8Nums, 2048),
    (twGtwelfthW1nHT9Labs, twGtwelfthW1nHT9Nums, 2048), (twGtwelfthW1nHT10Labs,
    twGtwelfthW1nHT10Nums, 2048), (twGtwelfthW1nHT11Labs, twGtwelfthW1nHT11Nums, 2048),
    (twGtwelfthW1nHT12Labs, twGtwelfthW1nHT12Nums, 2048), (twGtwelfthW1nHT13Labs,
    twGtwelfthW1nHT13Nums, 2048), (twGtwelfthW1nHT14Labs, twGtwelfthW1nHT14Nums, 2048),
    (twGtwelfthW1nHT15Labs, twGtwelfthW1nHT15Nums, 2048), (twGtwelfthW1nHT16Labs,
    twGtwelfthW1nHT16Nums, 2048), (twGtwelfthW1nHT17Labs, twGtwelfthW1nHT17Nums, 2048),
    (twGtwelfthW1nHT18Labs, twGtwelfthW1nHT18Nums, 2048), (twGtwelfthW1nHT19Labs,
    twGtwelfthW1nHT19Nums, 2048), (twGtwelfthW1nHT20Labs, twGtwelfthW1nHT20Nums, 2048),
    (twGtwelfthW1nHT21Labs, twGtwelfthW1nHT21Nums, 2048), (twGtwelfthW1nHT22Labs,
    twGtwelfthW1nHT22Nums, 1704)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem twGtwelfthW1n_Wsh : twGtwelfthW1nW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(twGtwelfthW1nGT0Labs, twGtwelfthW1nGT0Nums, 2048), (twGtwelfthW1nGT1Labs,
    twGtwelfthW1nGT1Nums, 2048), (twGtwelfthW1nGT2Labs, twGtwelfthW1nGT2Nums, 2048),
    (twGtwelfthW1nGT3Labs, twGtwelfthW1nGT3Nums, 2048), (twGtwelfthW1nGT4Labs,
    twGtwelfthW1nGT4Nums, 2048), (twGtwelfthW1nGT5Labs, twGtwelfthW1nGT5Nums, 2048),
    (twGtwelfthW1nGT6Labs, twGtwelfthW1nGT6Nums, 2048), (twGtwelfthW1nGT7Labs,
    twGtwelfthW1nGT7Nums, 2048), (twGtwelfthW1nGT8Labs, twGtwelfthW1nGT8Nums, 2048),
    (twGtwelfthW1nGT9Labs, twGtwelfthW1nGT9Nums, 2048), (twGtwelfthW1nGT10Labs,
    twGtwelfthW1nGT10Nums, 2048), (twGtwelfthW1nGT11Labs, twGtwelfthW1nGT11Nums, 2048),
    (twGtwelfthW1nGT12Labs, twGtwelfthW1nGT12Nums, 2048), (twGtwelfthW1nGT13Labs,
    twGtwelfthW1nGT13Nums, 2048), (twGtwelfthW1nGT14Labs, twGtwelfthW1nGT14Nums, 2048),
    (twGtwelfthW1nGT15Labs, twGtwelfthW1nGT15Nums, 2048), (twGtwelfthW1nGT16Labs,
    twGtwelfthW1nGT16Nums, 2048), (twGtwelfthW1nGT17Labs, twGtwelfthW1nGT17Nums, 2048),
    (twGtwelfthW1nGT18Labs, twGtwelfthW1nGT18Nums, 2048), (twGtwelfthW1nGT19Labs,
    twGtwelfthW1nGT19Nums, 2048), (twGtwelfthW1nGT20Labs, twGtwelfthW1nGT20Nums, 2048),
    (twGtwelfthW1nGT21Labs, twGtwelfthW1nGT21Nums, 2048), (twGtwelfthW1nGT22Labs,
    twGtwelfthW1nGT22Nums, 1704)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem twGtwelfthW1n_hok : octPackOk 64 twGtwelfthW1nL = true :=
  OctadDense.octPackOk_of_chk 64 5 false twGtwelfthW1nL _ _ 4073472 twGtwelfthW1n_Lsh
      twGtwelfthW1n_chk

/-- The octad integer sum. -/
theorem twGtwelfthW1n_octn : octSumZ 64 false twGtwelfthW1nL twGtwelfthW1nW = 4073472 :=
  OctadDense.octSumZ_of_chk 64 5 false twGtwelfthW1nL twGtwelfthW1nW _ _ 4073472 twGtwelfthW1n_Lsh
      twGtwelfthW1n_Wsh twGtwelfthW1n_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem twGtwelfthW1n_selfchk : OctadDense.selfOctChk 64 [(twGtwelfthW1nGT0Labs,
    twGtwelfthW1nGT0Nums, 2048), (twGtwelfthW1nGT1Labs, twGtwelfthW1nGT1Nums, 2048),
    (twGtwelfthW1nGT2Labs, twGtwelfthW1nGT2Nums, 2048), (twGtwelfthW1nGT3Labs,
    twGtwelfthW1nGT3Nums, 2048), (twGtwelfthW1nGT4Labs, twGtwelfthW1nGT4Nums, 2048),
    (twGtwelfthW1nGT5Labs, twGtwelfthW1nGT5Nums, 2048), (twGtwelfthW1nGT6Labs,
    twGtwelfthW1nGT6Nums, 2048), (twGtwelfthW1nGT7Labs, twGtwelfthW1nGT7Nums, 2048),
    (twGtwelfthW1nGT8Labs, twGtwelfthW1nGT8Nums, 2048), (twGtwelfthW1nGT9Labs,
    twGtwelfthW1nGT9Nums, 2048), (twGtwelfthW1nGT10Labs, twGtwelfthW1nGT10Nums, 2048),
    (twGtwelfthW1nGT11Labs, twGtwelfthW1nGT11Nums, 2048), (twGtwelfthW1nGT12Labs,
    twGtwelfthW1nGT12Nums, 2048), (twGtwelfthW1nGT13Labs, twGtwelfthW1nGT13Nums, 2048),
    (twGtwelfthW1nGT14Labs, twGtwelfthW1nGT14Nums, 2048), (twGtwelfthW1nGT15Labs,
    twGtwelfthW1nGT15Nums, 2048), (twGtwelfthW1nGT16Labs, twGtwelfthW1nGT16Nums, 2048),
    (twGtwelfthW1nGT17Labs, twGtwelfthW1nGT17Nums, 2048), (twGtwelfthW1nGT18Labs,
    twGtwelfthW1nGT18Nums, 2048), (twGtwelfthW1nGT19Labs, twGtwelfthW1nGT19Nums, 2048),
    (twGtwelfthW1nGT20Labs, twGtwelfthW1nGT20Nums, 2048), (twGtwelfthW1nGT21Labs,
    twGtwelfthW1nGT21Nums, 2048), (twGtwelfthW1nGT22Labs, twGtwelfthW1nGT22Nums, 1704)] 509184 =
    true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem twGtwelfthW1n_hn : twGtwelfthW1nL.sden * (octSumZ 64 false twGtwelfthW1nL twGtwelfthW1nW :
    ℚ) / 8 =
    twGtwelfthW1nW.sden * (selfOctP twGtwelfthW1nW : ℚ) := by
  rw [twGtwelfthW1n_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 twGtwelfthW1nW _ 509184
      twGtwelfthW1n_Wsh twGtwelfthW1n_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
