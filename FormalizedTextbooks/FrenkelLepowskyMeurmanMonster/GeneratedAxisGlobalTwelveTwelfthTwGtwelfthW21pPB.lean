/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW21pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (octads) of the identification Twelfth[9]+ <-> Twelfth[21]+ (record
gtwelfth:W21+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem twGtwelfthW21p_chk : OctadDense.octSumChk 64 5 true [(twGtwelfthW21pHT0Labs,
    twGtwelfthW21pHT0Nums, 2048), (twGtwelfthW21pHT1Labs, twGtwelfthW21pHT1Nums, 2048),
    (twGtwelfthW21pHT2Labs, twGtwelfthW21pHT2Nums, 2048), (twGtwelfthW21pHT3Labs,
    twGtwelfthW21pHT3Nums, 2048), (twGtwelfthW21pHT4Labs, twGtwelfthW21pHT4Nums, 2048),
    (twGtwelfthW21pHT5Labs, twGtwelfthW21pHT5Nums, 2048), (twGtwelfthW21pHT6Labs,
    twGtwelfthW21pHT6Nums, 2048), (twGtwelfthW21pHT7Labs, twGtwelfthW21pHT7Nums, 2048),
    (twGtwelfthW21pHT8Labs, twGtwelfthW21pHT8Nums, 2048), (twGtwelfthW21pHT9Labs,
    twGtwelfthW21pHT9Nums, 2048), (twGtwelfthW21pHT10Labs, twGtwelfthW21pHT10Nums, 2048),
    (twGtwelfthW21pHT11Labs, twGtwelfthW21pHT11Nums, 2048), (twGtwelfthW21pHT12Labs,
    twGtwelfthW21pHT12Nums, 2048), (twGtwelfthW21pHT13Labs, twGtwelfthW21pHT13Nums, 2048),
    (twGtwelfthW21pHT14Labs, twGtwelfthW21pHT14Nums, 2048), (twGtwelfthW21pHT15Labs,
    twGtwelfthW21pHT15Nums, 2048), (twGtwelfthW21pHT16Labs, twGtwelfthW21pHT16Nums, 2048),
    (twGtwelfthW21pHT17Labs, twGtwelfthW21pHT17Nums, 2048), (twGtwelfthW21pHT18Labs,
    twGtwelfthW21pHT18Nums, 2048), (twGtwelfthW21pHT19Labs, twGtwelfthW21pHT19Nums, 2048),
    (twGtwelfthW21pHT20Labs, twGtwelfthW21pHT20Nums, 2048), (twGtwelfthW21pHT21Labs,
    twGtwelfthW21pHT21Nums, 2048), (twGtwelfthW21pHT22Labs, twGtwelfthW21pHT22Nums, 1704)]
    [(twGtwelfthW21pGT0Labs, twGtwelfthW21pGT0Nums, 2048), (twGtwelfthW21pGT1Labs,
    twGtwelfthW21pGT1Nums, 2048), (twGtwelfthW21pGT2Labs, twGtwelfthW21pGT2Nums, 2048),
    (twGtwelfthW21pGT3Labs, twGtwelfthW21pGT3Nums, 2048), (twGtwelfthW21pGT4Labs,
    twGtwelfthW21pGT4Nums, 2048), (twGtwelfthW21pGT5Labs, twGtwelfthW21pGT5Nums, 2048),
    (twGtwelfthW21pGT6Labs, twGtwelfthW21pGT6Nums, 2048), (twGtwelfthW21pGT7Labs,
    twGtwelfthW21pGT7Nums, 2048), (twGtwelfthW21pGT8Labs, twGtwelfthW21pGT8Nums, 2048),
    (twGtwelfthW21pGT9Labs, twGtwelfthW21pGT9Nums, 2048), (twGtwelfthW21pGT10Labs,
    twGtwelfthW21pGT10Nums, 2048), (twGtwelfthW21pGT11Labs, twGtwelfthW21pGT11Nums, 2048),
    (twGtwelfthW21pGT12Labs, twGtwelfthW21pGT12Nums, 2048), (twGtwelfthW21pGT13Labs,
    twGtwelfthW21pGT13Nums, 2048), (twGtwelfthW21pGT14Labs, twGtwelfthW21pGT14Nums, 2048),
    (twGtwelfthW21pGT15Labs, twGtwelfthW21pGT15Nums, 2048), (twGtwelfthW21pGT16Labs,
    twGtwelfthW21pGT16Nums, 2048), (twGtwelfthW21pGT17Labs, twGtwelfthW21pGT17Nums, 2048),
    (twGtwelfthW21pGT18Labs, twGtwelfthW21pGT18Nums, 2048), (twGtwelfthW21pGT19Labs,
    twGtwelfthW21pGT19Nums, 2048), (twGtwelfthW21pGT20Labs, twGtwelfthW21pGT20Nums, 2048),
    (twGtwelfthW21pGT21Labs, twGtwelfthW21pGT21Nums, 2048), (twGtwelfthW21pGT22Labs,
    twGtwelfthW21pGT22Nums, 1704)] 4073472 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem twGtwelfthW21p_Lsh : twGtwelfthW21pL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(twGtwelfthW21pHT0Labs, twGtwelfthW21pHT0Nums, 2048), (twGtwelfthW21pHT1Labs,
    twGtwelfthW21pHT1Nums, 2048), (twGtwelfthW21pHT2Labs, twGtwelfthW21pHT2Nums, 2048),
    (twGtwelfthW21pHT3Labs, twGtwelfthW21pHT3Nums, 2048), (twGtwelfthW21pHT4Labs,
    twGtwelfthW21pHT4Nums, 2048), (twGtwelfthW21pHT5Labs, twGtwelfthW21pHT5Nums, 2048),
    (twGtwelfthW21pHT6Labs, twGtwelfthW21pHT6Nums, 2048), (twGtwelfthW21pHT7Labs,
    twGtwelfthW21pHT7Nums, 2048), (twGtwelfthW21pHT8Labs, twGtwelfthW21pHT8Nums, 2048),
    (twGtwelfthW21pHT9Labs, twGtwelfthW21pHT9Nums, 2048), (twGtwelfthW21pHT10Labs,
    twGtwelfthW21pHT10Nums, 2048), (twGtwelfthW21pHT11Labs, twGtwelfthW21pHT11Nums, 2048),
    (twGtwelfthW21pHT12Labs, twGtwelfthW21pHT12Nums, 2048), (twGtwelfthW21pHT13Labs,
    twGtwelfthW21pHT13Nums, 2048), (twGtwelfthW21pHT14Labs, twGtwelfthW21pHT14Nums, 2048),
    (twGtwelfthW21pHT15Labs, twGtwelfthW21pHT15Nums, 2048), (twGtwelfthW21pHT16Labs,
    twGtwelfthW21pHT16Nums, 2048), (twGtwelfthW21pHT17Labs, twGtwelfthW21pHT17Nums, 2048),
    (twGtwelfthW21pHT18Labs, twGtwelfthW21pHT18Nums, 2048), (twGtwelfthW21pHT19Labs,
    twGtwelfthW21pHT19Nums, 2048), (twGtwelfthW21pHT20Labs, twGtwelfthW21pHT20Nums, 2048),
    (twGtwelfthW21pHT21Labs, twGtwelfthW21pHT21Nums, 2048), (twGtwelfthW21pHT22Labs,
    twGtwelfthW21pHT22Nums, 1704)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem twGtwelfthW21p_Wsh : twGtwelfthW21pW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(twGtwelfthW21pGT0Labs, twGtwelfthW21pGT0Nums, 2048), (twGtwelfthW21pGT1Labs,
    twGtwelfthW21pGT1Nums, 2048), (twGtwelfthW21pGT2Labs, twGtwelfthW21pGT2Nums, 2048),
    (twGtwelfthW21pGT3Labs, twGtwelfthW21pGT3Nums, 2048), (twGtwelfthW21pGT4Labs,
    twGtwelfthW21pGT4Nums, 2048), (twGtwelfthW21pGT5Labs, twGtwelfthW21pGT5Nums, 2048),
    (twGtwelfthW21pGT6Labs, twGtwelfthW21pGT6Nums, 2048), (twGtwelfthW21pGT7Labs,
    twGtwelfthW21pGT7Nums, 2048), (twGtwelfthW21pGT8Labs, twGtwelfthW21pGT8Nums, 2048),
    (twGtwelfthW21pGT9Labs, twGtwelfthW21pGT9Nums, 2048), (twGtwelfthW21pGT10Labs,
    twGtwelfthW21pGT10Nums, 2048), (twGtwelfthW21pGT11Labs, twGtwelfthW21pGT11Nums, 2048),
    (twGtwelfthW21pGT12Labs, twGtwelfthW21pGT12Nums, 2048), (twGtwelfthW21pGT13Labs,
    twGtwelfthW21pGT13Nums, 2048), (twGtwelfthW21pGT14Labs, twGtwelfthW21pGT14Nums, 2048),
    (twGtwelfthW21pGT15Labs, twGtwelfthW21pGT15Nums, 2048), (twGtwelfthW21pGT16Labs,
    twGtwelfthW21pGT16Nums, 2048), (twGtwelfthW21pGT17Labs, twGtwelfthW21pGT17Nums, 2048),
    (twGtwelfthW21pGT18Labs, twGtwelfthW21pGT18Nums, 2048), (twGtwelfthW21pGT19Labs,
    twGtwelfthW21pGT19Nums, 2048), (twGtwelfthW21pGT20Labs, twGtwelfthW21pGT20Nums, 2048),
    (twGtwelfthW21pGT21Labs, twGtwelfthW21pGT21Nums, 2048), (twGtwelfthW21pGT22Labs,
    twGtwelfthW21pGT22Nums, 1704)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem twGtwelfthW21p_hok : octPackOk 64 twGtwelfthW21pL = true :=
  OctadDense.octPackOk_of_chk 64 5 true twGtwelfthW21pL _ _ 4073472 twGtwelfthW21p_Lsh
      twGtwelfthW21p_chk

/-- The octad integer sum. -/
theorem twGtwelfthW21p_octn : octSumZ 64 true twGtwelfthW21pL twGtwelfthW21pW = 4073472 :=
  OctadDense.octSumZ_of_chk 64 5 true twGtwelfthW21pL twGtwelfthW21pW _ _ 4073472
      twGtwelfthW21p_Lsh twGtwelfthW21p_Wsh twGtwelfthW21p_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem twGtwelfthW21p_selfchk : OctadDense.selfOctChk 64 [(twGtwelfthW21pGT0Labs,
    twGtwelfthW21pGT0Nums, 2048), (twGtwelfthW21pGT1Labs, twGtwelfthW21pGT1Nums, 2048),
    (twGtwelfthW21pGT2Labs, twGtwelfthW21pGT2Nums, 2048), (twGtwelfthW21pGT3Labs,
    twGtwelfthW21pGT3Nums, 2048), (twGtwelfthW21pGT4Labs, twGtwelfthW21pGT4Nums, 2048),
    (twGtwelfthW21pGT5Labs, twGtwelfthW21pGT5Nums, 2048), (twGtwelfthW21pGT6Labs,
    twGtwelfthW21pGT6Nums, 2048), (twGtwelfthW21pGT7Labs, twGtwelfthW21pGT7Nums, 2048),
    (twGtwelfthW21pGT8Labs, twGtwelfthW21pGT8Nums, 2048), (twGtwelfthW21pGT9Labs,
    twGtwelfthW21pGT9Nums, 2048), (twGtwelfthW21pGT10Labs, twGtwelfthW21pGT10Nums, 2048),
    (twGtwelfthW21pGT11Labs, twGtwelfthW21pGT11Nums, 2048), (twGtwelfthW21pGT12Labs,
    twGtwelfthW21pGT12Nums, 2048), (twGtwelfthW21pGT13Labs, twGtwelfthW21pGT13Nums, 2048),
    (twGtwelfthW21pGT14Labs, twGtwelfthW21pGT14Nums, 2048), (twGtwelfthW21pGT15Labs,
    twGtwelfthW21pGT15Nums, 2048), (twGtwelfthW21pGT16Labs, twGtwelfthW21pGT16Nums, 2048),
    (twGtwelfthW21pGT17Labs, twGtwelfthW21pGT17Nums, 2048), (twGtwelfthW21pGT18Labs,
    twGtwelfthW21pGT18Nums, 2048), (twGtwelfthW21pGT19Labs, twGtwelfthW21pGT19Nums, 2048),
    (twGtwelfthW21pGT20Labs, twGtwelfthW21pGT20Nums, 2048), (twGtwelfthW21pGT21Labs,
    twGtwelfthW21pGT21Nums, 2048), (twGtwelfthW21pGT22Labs, twGtwelfthW21pGT22Nums, 1704)] 509184
    = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem twGtwelfthW21p_hn : twGtwelfthW21pL.sden * (octSumZ 64 true twGtwelfthW21pL
    twGtwelfthW21pW : ℚ) / 8 =
    twGtwelfthW21pW.sden * (selfOctP twGtwelfthW21pW : ℚ) := by
  rw [twGtwelfthW21p_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 twGtwelfthW21pW _ 509184
      twGtwelfthW21p_Wsh twGtwelfthW21p_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
