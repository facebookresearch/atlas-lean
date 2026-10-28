/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW9pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (octads) of the identification Twelfth[9]+ <-> Twelfth[21]- (record
gtwelfth:W9+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem twGtwelfthW9p_chk : OctadDense.octSumChk 64 5 true [(twGtwelfthW9pHT0Labs,
    twGtwelfthW9pHT0Nums, 2048), (twGtwelfthW9pHT1Labs, twGtwelfthW9pHT1Nums, 2048),
    (twGtwelfthW9pHT2Labs, twGtwelfthW9pHT2Nums, 2048), (twGtwelfthW9pHT3Labs,
    twGtwelfthW9pHT3Nums, 2048), (twGtwelfthW9pHT4Labs, twGtwelfthW9pHT4Nums, 2048),
    (twGtwelfthW9pHT5Labs, twGtwelfthW9pHT5Nums, 2048), (twGtwelfthW9pHT6Labs,
    twGtwelfthW9pHT6Nums, 2048), (twGtwelfthW9pHT7Labs, twGtwelfthW9pHT7Nums, 2048),
    (twGtwelfthW9pHT8Labs, twGtwelfthW9pHT8Nums, 2048), (twGtwelfthW9pHT9Labs,
    twGtwelfthW9pHT9Nums, 2048), (twGtwelfthW9pHT10Labs, twGtwelfthW9pHT10Nums, 2048),
    (twGtwelfthW9pHT11Labs, twGtwelfthW9pHT11Nums, 2048), (twGtwelfthW9pHT12Labs,
    twGtwelfthW9pHT12Nums, 2048), (twGtwelfthW9pHT13Labs, twGtwelfthW9pHT13Nums, 2048),
    (twGtwelfthW9pHT14Labs, twGtwelfthW9pHT14Nums, 2048), (twGtwelfthW9pHT15Labs,
    twGtwelfthW9pHT15Nums, 2048), (twGtwelfthW9pHT16Labs, twGtwelfthW9pHT16Nums, 2048),
    (twGtwelfthW9pHT17Labs, twGtwelfthW9pHT17Nums, 2048), (twGtwelfthW9pHT18Labs,
    twGtwelfthW9pHT18Nums, 2048), (twGtwelfthW9pHT19Labs, twGtwelfthW9pHT19Nums, 2048),
    (twGtwelfthW9pHT20Labs, twGtwelfthW9pHT20Nums, 2048), (twGtwelfthW9pHT21Labs,
    twGtwelfthW9pHT21Nums, 2048), (twGtwelfthW9pHT22Labs, twGtwelfthW9pHT22Nums, 1704)]
    [(twGtwelfthW9pGT0Labs, twGtwelfthW9pGT0Nums, 2048), (twGtwelfthW9pGT1Labs,
    twGtwelfthW9pGT1Nums, 2048), (twGtwelfthW9pGT2Labs, twGtwelfthW9pGT2Nums, 2048),
    (twGtwelfthW9pGT3Labs, twGtwelfthW9pGT3Nums, 2048), (twGtwelfthW9pGT4Labs,
    twGtwelfthW9pGT4Nums, 2048), (twGtwelfthW9pGT5Labs, twGtwelfthW9pGT5Nums, 2048),
    (twGtwelfthW9pGT6Labs, twGtwelfthW9pGT6Nums, 2048), (twGtwelfthW9pGT7Labs,
    twGtwelfthW9pGT7Nums, 2048), (twGtwelfthW9pGT8Labs, twGtwelfthW9pGT8Nums, 2048),
    (twGtwelfthW9pGT9Labs, twGtwelfthW9pGT9Nums, 2048), (twGtwelfthW9pGT10Labs,
    twGtwelfthW9pGT10Nums, 2048), (twGtwelfthW9pGT11Labs, twGtwelfthW9pGT11Nums, 2048),
    (twGtwelfthW9pGT12Labs, twGtwelfthW9pGT12Nums, 2048), (twGtwelfthW9pGT13Labs,
    twGtwelfthW9pGT13Nums, 2048), (twGtwelfthW9pGT14Labs, twGtwelfthW9pGT14Nums, 2048),
    (twGtwelfthW9pGT15Labs, twGtwelfthW9pGT15Nums, 2048), (twGtwelfthW9pGT16Labs,
    twGtwelfthW9pGT16Nums, 2048), (twGtwelfthW9pGT17Labs, twGtwelfthW9pGT17Nums, 2048),
    (twGtwelfthW9pGT18Labs, twGtwelfthW9pGT18Nums, 2048), (twGtwelfthW9pGT19Labs,
    twGtwelfthW9pGT19Nums, 2048), (twGtwelfthW9pGT20Labs, twGtwelfthW9pGT20Nums, 2048),
    (twGtwelfthW9pGT21Labs, twGtwelfthW9pGT21Nums, 2048), (twGtwelfthW9pGT22Labs,
    twGtwelfthW9pGT22Nums, 1704)] 4073472 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem twGtwelfthW9p_Lsh : twGtwelfthW9pL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(twGtwelfthW9pHT0Labs, twGtwelfthW9pHT0Nums, 2048), (twGtwelfthW9pHT1Labs,
    twGtwelfthW9pHT1Nums, 2048), (twGtwelfthW9pHT2Labs, twGtwelfthW9pHT2Nums, 2048),
    (twGtwelfthW9pHT3Labs, twGtwelfthW9pHT3Nums, 2048), (twGtwelfthW9pHT4Labs,
    twGtwelfthW9pHT4Nums, 2048), (twGtwelfthW9pHT5Labs, twGtwelfthW9pHT5Nums, 2048),
    (twGtwelfthW9pHT6Labs, twGtwelfthW9pHT6Nums, 2048), (twGtwelfthW9pHT7Labs,
    twGtwelfthW9pHT7Nums, 2048), (twGtwelfthW9pHT8Labs, twGtwelfthW9pHT8Nums, 2048),
    (twGtwelfthW9pHT9Labs, twGtwelfthW9pHT9Nums, 2048), (twGtwelfthW9pHT10Labs,
    twGtwelfthW9pHT10Nums, 2048), (twGtwelfthW9pHT11Labs, twGtwelfthW9pHT11Nums, 2048),
    (twGtwelfthW9pHT12Labs, twGtwelfthW9pHT12Nums, 2048), (twGtwelfthW9pHT13Labs,
    twGtwelfthW9pHT13Nums, 2048), (twGtwelfthW9pHT14Labs, twGtwelfthW9pHT14Nums, 2048),
    (twGtwelfthW9pHT15Labs, twGtwelfthW9pHT15Nums, 2048), (twGtwelfthW9pHT16Labs,
    twGtwelfthW9pHT16Nums, 2048), (twGtwelfthW9pHT17Labs, twGtwelfthW9pHT17Nums, 2048),
    (twGtwelfthW9pHT18Labs, twGtwelfthW9pHT18Nums, 2048), (twGtwelfthW9pHT19Labs,
    twGtwelfthW9pHT19Nums, 2048), (twGtwelfthW9pHT20Labs, twGtwelfthW9pHT20Nums, 2048),
    (twGtwelfthW9pHT21Labs, twGtwelfthW9pHT21Nums, 2048), (twGtwelfthW9pHT22Labs,
    twGtwelfthW9pHT22Nums, 1704)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem twGtwelfthW9p_Wsh : twGtwelfthW9pW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(twGtwelfthW9pGT0Labs, twGtwelfthW9pGT0Nums, 2048), (twGtwelfthW9pGT1Labs,
    twGtwelfthW9pGT1Nums, 2048), (twGtwelfthW9pGT2Labs, twGtwelfthW9pGT2Nums, 2048),
    (twGtwelfthW9pGT3Labs, twGtwelfthW9pGT3Nums, 2048), (twGtwelfthW9pGT4Labs,
    twGtwelfthW9pGT4Nums, 2048), (twGtwelfthW9pGT5Labs, twGtwelfthW9pGT5Nums, 2048),
    (twGtwelfthW9pGT6Labs, twGtwelfthW9pGT6Nums, 2048), (twGtwelfthW9pGT7Labs,
    twGtwelfthW9pGT7Nums, 2048), (twGtwelfthW9pGT8Labs, twGtwelfthW9pGT8Nums, 2048),
    (twGtwelfthW9pGT9Labs, twGtwelfthW9pGT9Nums, 2048), (twGtwelfthW9pGT10Labs,
    twGtwelfthW9pGT10Nums, 2048), (twGtwelfthW9pGT11Labs, twGtwelfthW9pGT11Nums, 2048),
    (twGtwelfthW9pGT12Labs, twGtwelfthW9pGT12Nums, 2048), (twGtwelfthW9pGT13Labs,
    twGtwelfthW9pGT13Nums, 2048), (twGtwelfthW9pGT14Labs, twGtwelfthW9pGT14Nums, 2048),
    (twGtwelfthW9pGT15Labs, twGtwelfthW9pGT15Nums, 2048), (twGtwelfthW9pGT16Labs,
    twGtwelfthW9pGT16Nums, 2048), (twGtwelfthW9pGT17Labs, twGtwelfthW9pGT17Nums, 2048),
    (twGtwelfthW9pGT18Labs, twGtwelfthW9pGT18Nums, 2048), (twGtwelfthW9pGT19Labs,
    twGtwelfthW9pGT19Nums, 2048), (twGtwelfthW9pGT20Labs, twGtwelfthW9pGT20Nums, 2048),
    (twGtwelfthW9pGT21Labs, twGtwelfthW9pGT21Nums, 2048), (twGtwelfthW9pGT22Labs,
    twGtwelfthW9pGT22Nums, 1704)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem twGtwelfthW9p_hok : octPackOk 64 twGtwelfthW9pL = true :=
  OctadDense.octPackOk_of_chk 64 5 true twGtwelfthW9pL _ _ 4073472 twGtwelfthW9p_Lsh
      twGtwelfthW9p_chk

/-- The octad integer sum. -/
theorem twGtwelfthW9p_octn : octSumZ 64 true twGtwelfthW9pL twGtwelfthW9pW = 4073472 :=
  OctadDense.octSumZ_of_chk 64 5 true twGtwelfthW9pL twGtwelfthW9pW _ _ 4073472 twGtwelfthW9p_Lsh
      twGtwelfthW9p_Wsh twGtwelfthW9p_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem twGtwelfthW9p_selfchk : OctadDense.selfOctChk 64 [(twGtwelfthW9pGT0Labs,
    twGtwelfthW9pGT0Nums, 2048), (twGtwelfthW9pGT1Labs, twGtwelfthW9pGT1Nums, 2048),
    (twGtwelfthW9pGT2Labs, twGtwelfthW9pGT2Nums, 2048), (twGtwelfthW9pGT3Labs,
    twGtwelfthW9pGT3Nums, 2048), (twGtwelfthW9pGT4Labs, twGtwelfthW9pGT4Nums, 2048),
    (twGtwelfthW9pGT5Labs, twGtwelfthW9pGT5Nums, 2048), (twGtwelfthW9pGT6Labs,
    twGtwelfthW9pGT6Nums, 2048), (twGtwelfthW9pGT7Labs, twGtwelfthW9pGT7Nums, 2048),
    (twGtwelfthW9pGT8Labs, twGtwelfthW9pGT8Nums, 2048), (twGtwelfthW9pGT9Labs,
    twGtwelfthW9pGT9Nums, 2048), (twGtwelfthW9pGT10Labs, twGtwelfthW9pGT10Nums, 2048),
    (twGtwelfthW9pGT11Labs, twGtwelfthW9pGT11Nums, 2048), (twGtwelfthW9pGT12Labs,
    twGtwelfthW9pGT12Nums, 2048), (twGtwelfthW9pGT13Labs, twGtwelfthW9pGT13Nums, 2048),
    (twGtwelfthW9pGT14Labs, twGtwelfthW9pGT14Nums, 2048), (twGtwelfthW9pGT15Labs,
    twGtwelfthW9pGT15Nums, 2048), (twGtwelfthW9pGT16Labs, twGtwelfthW9pGT16Nums, 2048),
    (twGtwelfthW9pGT17Labs, twGtwelfthW9pGT17Nums, 2048), (twGtwelfthW9pGT18Labs,
    twGtwelfthW9pGT18Nums, 2048), (twGtwelfthW9pGT19Labs, twGtwelfthW9pGT19Nums, 2048),
    (twGtwelfthW9pGT20Labs, twGtwelfthW9pGT20Nums, 2048), (twGtwelfthW9pGT21Labs,
    twGtwelfthW9pGT21Nums, 2048), (twGtwelfthW9pGT22Labs, twGtwelfthW9pGT22Nums, 1704)] 509184 =
    true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem twGtwelfthW9p_hn : twGtwelfthW9pL.sden * (octSumZ 64 true twGtwelfthW9pL twGtwelfthW9pW :
    ℚ) / 8 =
    twGtwelfthW9pW.sden * (selfOctP twGtwelfthW9pW : ℚ) := by
  rw [twGtwelfthW9p_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 twGtwelfthW9pW _ 509184
      twGtwelfthW9p_Wsh twGtwelfthW9p_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
