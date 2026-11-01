/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW13pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (octads) of the identification Twelfth[13]- <-> Twelfth[13]+ (record
gtwelfth:W13+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem twGtwelfthW13p_chk : OctadDense.octSumChk 64 5 true [(twGtwelfthW13pHT0Labs,
    twGtwelfthW13pHT0Nums, 2048), (twGtwelfthW13pHT1Labs, twGtwelfthW13pHT1Nums, 2048),
    (twGtwelfthW13pHT2Labs, twGtwelfthW13pHT2Nums, 2048), (twGtwelfthW13pHT3Labs,
    twGtwelfthW13pHT3Nums, 2048), (twGtwelfthW13pHT4Labs, twGtwelfthW13pHT4Nums, 2048),
    (twGtwelfthW13pHT5Labs, twGtwelfthW13pHT5Nums, 2048), (twGtwelfthW13pHT6Labs,
    twGtwelfthW13pHT6Nums, 2048), (twGtwelfthW13pHT7Labs, twGtwelfthW13pHT7Nums, 2048),
    (twGtwelfthW13pHT8Labs, twGtwelfthW13pHT8Nums, 2048), (twGtwelfthW13pHT9Labs,
    twGtwelfthW13pHT9Nums, 2048), (twGtwelfthW13pHT10Labs, twGtwelfthW13pHT10Nums, 2048),
    (twGtwelfthW13pHT11Labs, twGtwelfthW13pHT11Nums, 2048), (twGtwelfthW13pHT12Labs,
    twGtwelfthW13pHT12Nums, 2048), (twGtwelfthW13pHT13Labs, twGtwelfthW13pHT13Nums, 2048),
    (twGtwelfthW13pHT14Labs, twGtwelfthW13pHT14Nums, 2048), (twGtwelfthW13pHT15Labs,
    twGtwelfthW13pHT15Nums, 2048), (twGtwelfthW13pHT16Labs, twGtwelfthW13pHT16Nums, 2048),
    (twGtwelfthW13pHT17Labs, twGtwelfthW13pHT17Nums, 2048), (twGtwelfthW13pHT18Labs,
    twGtwelfthW13pHT18Nums, 2048), (twGtwelfthW13pHT19Labs, twGtwelfthW13pHT19Nums, 2048),
    (twGtwelfthW13pHT20Labs, twGtwelfthW13pHT20Nums, 2048), (twGtwelfthW13pHT21Labs,
    twGtwelfthW13pHT21Nums, 2048), (twGtwelfthW13pHT22Labs, twGtwelfthW13pHT22Nums, 1704)]
    [(twGtwelfthW13pGT0Labs, twGtwelfthW13pGT0Nums, 2048), (twGtwelfthW13pGT1Labs,
    twGtwelfthW13pGT1Nums, 2048), (twGtwelfthW13pGT2Labs, twGtwelfthW13pGT2Nums, 2048),
    (twGtwelfthW13pGT3Labs, twGtwelfthW13pGT3Nums, 2048), (twGtwelfthW13pGT4Labs,
    twGtwelfthW13pGT4Nums, 2048), (twGtwelfthW13pGT5Labs, twGtwelfthW13pGT5Nums, 2048),
    (twGtwelfthW13pGT6Labs, twGtwelfthW13pGT6Nums, 2048), (twGtwelfthW13pGT7Labs,
    twGtwelfthW13pGT7Nums, 2048), (twGtwelfthW13pGT8Labs, twGtwelfthW13pGT8Nums, 2048),
    (twGtwelfthW13pGT9Labs, twGtwelfthW13pGT9Nums, 2048), (twGtwelfthW13pGT10Labs,
    twGtwelfthW13pGT10Nums, 2048), (twGtwelfthW13pGT11Labs, twGtwelfthW13pGT11Nums, 2048),
    (twGtwelfthW13pGT12Labs, twGtwelfthW13pGT12Nums, 2048), (twGtwelfthW13pGT13Labs,
    twGtwelfthW13pGT13Nums, 2048), (twGtwelfthW13pGT14Labs, twGtwelfthW13pGT14Nums, 2048),
    (twGtwelfthW13pGT15Labs, twGtwelfthW13pGT15Nums, 2048), (twGtwelfthW13pGT16Labs,
    twGtwelfthW13pGT16Nums, 2048), (twGtwelfthW13pGT17Labs, twGtwelfthW13pGT17Nums, 2048),
    (twGtwelfthW13pGT18Labs, twGtwelfthW13pGT18Nums, 2048), (twGtwelfthW13pGT19Labs,
    twGtwelfthW13pGT19Nums, 2048), (twGtwelfthW13pGT20Labs, twGtwelfthW13pGT20Nums, 2048),
    (twGtwelfthW13pGT21Labs, twGtwelfthW13pGT21Nums, 2048), (twGtwelfthW13pGT22Labs,
    twGtwelfthW13pGT22Nums, 1704)] 4073472 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem twGtwelfthW13p_Lsh : twGtwelfthW13pL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(twGtwelfthW13pHT0Labs, twGtwelfthW13pHT0Nums, 2048), (twGtwelfthW13pHT1Labs,
    twGtwelfthW13pHT1Nums, 2048), (twGtwelfthW13pHT2Labs, twGtwelfthW13pHT2Nums, 2048),
    (twGtwelfthW13pHT3Labs, twGtwelfthW13pHT3Nums, 2048), (twGtwelfthW13pHT4Labs,
    twGtwelfthW13pHT4Nums, 2048), (twGtwelfthW13pHT5Labs, twGtwelfthW13pHT5Nums, 2048),
    (twGtwelfthW13pHT6Labs, twGtwelfthW13pHT6Nums, 2048), (twGtwelfthW13pHT7Labs,
    twGtwelfthW13pHT7Nums, 2048), (twGtwelfthW13pHT8Labs, twGtwelfthW13pHT8Nums, 2048),
    (twGtwelfthW13pHT9Labs, twGtwelfthW13pHT9Nums, 2048), (twGtwelfthW13pHT10Labs,
    twGtwelfthW13pHT10Nums, 2048), (twGtwelfthW13pHT11Labs, twGtwelfthW13pHT11Nums, 2048),
    (twGtwelfthW13pHT12Labs, twGtwelfthW13pHT12Nums, 2048), (twGtwelfthW13pHT13Labs,
    twGtwelfthW13pHT13Nums, 2048), (twGtwelfthW13pHT14Labs, twGtwelfthW13pHT14Nums, 2048),
    (twGtwelfthW13pHT15Labs, twGtwelfthW13pHT15Nums, 2048), (twGtwelfthW13pHT16Labs,
    twGtwelfthW13pHT16Nums, 2048), (twGtwelfthW13pHT17Labs, twGtwelfthW13pHT17Nums, 2048),
    (twGtwelfthW13pHT18Labs, twGtwelfthW13pHT18Nums, 2048), (twGtwelfthW13pHT19Labs,
    twGtwelfthW13pHT19Nums, 2048), (twGtwelfthW13pHT20Labs, twGtwelfthW13pHT20Nums, 2048),
    (twGtwelfthW13pHT21Labs, twGtwelfthW13pHT21Nums, 2048), (twGtwelfthW13pHT22Labs,
    twGtwelfthW13pHT22Nums, 1704)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem twGtwelfthW13p_Wsh : twGtwelfthW13pW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(twGtwelfthW13pGT0Labs, twGtwelfthW13pGT0Nums, 2048), (twGtwelfthW13pGT1Labs,
    twGtwelfthW13pGT1Nums, 2048), (twGtwelfthW13pGT2Labs, twGtwelfthW13pGT2Nums, 2048),
    (twGtwelfthW13pGT3Labs, twGtwelfthW13pGT3Nums, 2048), (twGtwelfthW13pGT4Labs,
    twGtwelfthW13pGT4Nums, 2048), (twGtwelfthW13pGT5Labs, twGtwelfthW13pGT5Nums, 2048),
    (twGtwelfthW13pGT6Labs, twGtwelfthW13pGT6Nums, 2048), (twGtwelfthW13pGT7Labs,
    twGtwelfthW13pGT7Nums, 2048), (twGtwelfthW13pGT8Labs, twGtwelfthW13pGT8Nums, 2048),
    (twGtwelfthW13pGT9Labs, twGtwelfthW13pGT9Nums, 2048), (twGtwelfthW13pGT10Labs,
    twGtwelfthW13pGT10Nums, 2048), (twGtwelfthW13pGT11Labs, twGtwelfthW13pGT11Nums, 2048),
    (twGtwelfthW13pGT12Labs, twGtwelfthW13pGT12Nums, 2048), (twGtwelfthW13pGT13Labs,
    twGtwelfthW13pGT13Nums, 2048), (twGtwelfthW13pGT14Labs, twGtwelfthW13pGT14Nums, 2048),
    (twGtwelfthW13pGT15Labs, twGtwelfthW13pGT15Nums, 2048), (twGtwelfthW13pGT16Labs,
    twGtwelfthW13pGT16Nums, 2048), (twGtwelfthW13pGT17Labs, twGtwelfthW13pGT17Nums, 2048),
    (twGtwelfthW13pGT18Labs, twGtwelfthW13pGT18Nums, 2048), (twGtwelfthW13pGT19Labs,
    twGtwelfthW13pGT19Nums, 2048), (twGtwelfthW13pGT20Labs, twGtwelfthW13pGT20Nums, 2048),
    (twGtwelfthW13pGT21Labs, twGtwelfthW13pGT21Nums, 2048), (twGtwelfthW13pGT22Labs,
    twGtwelfthW13pGT22Nums, 1704)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem twGtwelfthW13p_hok : octPackOk 64 twGtwelfthW13pL = true :=
  OctadDense.octPackOk_of_chk 64 5 true twGtwelfthW13pL _ _ 4073472 twGtwelfthW13p_Lsh
      twGtwelfthW13p_chk

/-- The octad integer sum. -/
theorem twGtwelfthW13p_octn : octSumZ 64 true twGtwelfthW13pL twGtwelfthW13pW = 4073472 :=
  OctadDense.octSumZ_of_chk 64 5 true twGtwelfthW13pL twGtwelfthW13pW _ _ 4073472
      twGtwelfthW13p_Lsh twGtwelfthW13p_Wsh twGtwelfthW13p_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem twGtwelfthW13p_selfchk : OctadDense.selfOctChk 64 [(twGtwelfthW13pGT0Labs,
    twGtwelfthW13pGT0Nums, 2048), (twGtwelfthW13pGT1Labs, twGtwelfthW13pGT1Nums, 2048),
    (twGtwelfthW13pGT2Labs, twGtwelfthW13pGT2Nums, 2048), (twGtwelfthW13pGT3Labs,
    twGtwelfthW13pGT3Nums, 2048), (twGtwelfthW13pGT4Labs, twGtwelfthW13pGT4Nums, 2048),
    (twGtwelfthW13pGT5Labs, twGtwelfthW13pGT5Nums, 2048), (twGtwelfthW13pGT6Labs,
    twGtwelfthW13pGT6Nums, 2048), (twGtwelfthW13pGT7Labs, twGtwelfthW13pGT7Nums, 2048),
    (twGtwelfthW13pGT8Labs, twGtwelfthW13pGT8Nums, 2048), (twGtwelfthW13pGT9Labs,
    twGtwelfthW13pGT9Nums, 2048), (twGtwelfthW13pGT10Labs, twGtwelfthW13pGT10Nums, 2048),
    (twGtwelfthW13pGT11Labs, twGtwelfthW13pGT11Nums, 2048), (twGtwelfthW13pGT12Labs,
    twGtwelfthW13pGT12Nums, 2048), (twGtwelfthW13pGT13Labs, twGtwelfthW13pGT13Nums, 2048),
    (twGtwelfthW13pGT14Labs, twGtwelfthW13pGT14Nums, 2048), (twGtwelfthW13pGT15Labs,
    twGtwelfthW13pGT15Nums, 2048), (twGtwelfthW13pGT16Labs, twGtwelfthW13pGT16Nums, 2048),
    (twGtwelfthW13pGT17Labs, twGtwelfthW13pGT17Nums, 2048), (twGtwelfthW13pGT18Labs,
    twGtwelfthW13pGT18Nums, 2048), (twGtwelfthW13pGT19Labs, twGtwelfthW13pGT19Nums, 2048),
    (twGtwelfthW13pGT20Labs, twGtwelfthW13pGT20Nums, 2048), (twGtwelfthW13pGT21Labs,
    twGtwelfthW13pGT21Nums, 2048), (twGtwelfthW13pGT22Labs, twGtwelfthW13pGT22Nums, 1704)] 509184
    = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem twGtwelfthW13p_hn : twGtwelfthW13pL.sden * (octSumZ 64 true twGtwelfthW13pL
    twGtwelfthW13pW : ℚ) / 8 =
    twGtwelfthW13pW.sden * (selfOctP twGtwelfthW13pW : ℚ) := by
  rw [twGtwelfthW13p_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 twGtwelfthW13pW _ 509184
      twGtwelfthW13p_Wsh twGtwelfthW13p_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
