/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW36pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (octads) of the identification Twelfth[36]+ <-> Twelfth[36]+ (record
gtwelfth:W36+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The dense octad check (gtenth's `OctadDense`): field bounds and the octad sum value. -/
theorem twGtwelfthW36p_chk : OctadDense.octSumChk 64 5 true [(twGtwelfthW36pHT0Labs,
    twGtwelfthW36pHT0Nums, 2048), (twGtwelfthW36pHT1Labs, twGtwelfthW36pHT1Nums, 2048),
    (twGtwelfthW36pHT2Labs, twGtwelfthW36pHT2Nums, 2048), (twGtwelfthW36pHT3Labs,
    twGtwelfthW36pHT3Nums, 2048), (twGtwelfthW36pHT4Labs, twGtwelfthW36pHT4Nums, 2048),
    (twGtwelfthW36pHT5Labs, twGtwelfthW36pHT5Nums, 2048), (twGtwelfthW36pHT6Labs,
    twGtwelfthW36pHT6Nums, 2048), (twGtwelfthW36pHT7Labs, twGtwelfthW36pHT7Nums, 2048),
    (twGtwelfthW36pHT8Labs, twGtwelfthW36pHT8Nums, 2048), (twGtwelfthW36pHT9Labs,
    twGtwelfthW36pHT9Nums, 2048), (twGtwelfthW36pHT10Labs, twGtwelfthW36pHT10Nums, 2048),
    (twGtwelfthW36pHT11Labs, twGtwelfthW36pHT11Nums, 2048), (twGtwelfthW36pHT12Labs,
    twGtwelfthW36pHT12Nums, 2048), (twGtwelfthW36pHT13Labs, twGtwelfthW36pHT13Nums, 2048),
    (twGtwelfthW36pHT14Labs, twGtwelfthW36pHT14Nums, 2048), (twGtwelfthW36pHT15Labs,
    twGtwelfthW36pHT15Nums, 2048), (twGtwelfthW36pHT16Labs, twGtwelfthW36pHT16Nums, 2048),
    (twGtwelfthW36pHT17Labs, twGtwelfthW36pHT17Nums, 2048), (twGtwelfthW36pHT18Labs,
    twGtwelfthW36pHT18Nums, 2048), (twGtwelfthW36pHT19Labs, twGtwelfthW36pHT19Nums, 2048),
    (twGtwelfthW36pHT20Labs, twGtwelfthW36pHT20Nums, 2048), (twGtwelfthW36pHT21Labs,
    twGtwelfthW36pHT21Nums, 2048), (twGtwelfthW36pHT22Labs, twGtwelfthW36pHT22Nums, 1704)]
    [(twGtwelfthW36pGT0Labs, twGtwelfthW36pGT0Nums, 2048), (twGtwelfthW36pGT1Labs,
    twGtwelfthW36pGT1Nums, 2048), (twGtwelfthW36pGT2Labs, twGtwelfthW36pGT2Nums, 2048),
    (twGtwelfthW36pGT3Labs, twGtwelfthW36pGT3Nums, 2048), (twGtwelfthW36pGT4Labs,
    twGtwelfthW36pGT4Nums, 2048), (twGtwelfthW36pGT5Labs, twGtwelfthW36pGT5Nums, 2048),
    (twGtwelfthW36pGT6Labs, twGtwelfthW36pGT6Nums, 2048), (twGtwelfthW36pGT7Labs,
    twGtwelfthW36pGT7Nums, 2048), (twGtwelfthW36pGT8Labs, twGtwelfthW36pGT8Nums, 2048),
    (twGtwelfthW36pGT9Labs, twGtwelfthW36pGT9Nums, 2048), (twGtwelfthW36pGT10Labs,
    twGtwelfthW36pGT10Nums, 2048), (twGtwelfthW36pGT11Labs, twGtwelfthW36pGT11Nums, 2048),
    (twGtwelfthW36pGT12Labs, twGtwelfthW36pGT12Nums, 2048), (twGtwelfthW36pGT13Labs,
    twGtwelfthW36pGT13Nums, 2048), (twGtwelfthW36pGT14Labs, twGtwelfthW36pGT14Nums, 2048),
    (twGtwelfthW36pGT15Labs, twGtwelfthW36pGT15Nums, 2048), (twGtwelfthW36pGT16Labs,
    twGtwelfthW36pGT16Nums, 2048), (twGtwelfthW36pGT17Labs, twGtwelfthW36pGT17Nums, 2048),
    (twGtwelfthW36pGT18Labs, twGtwelfthW36pGT18Nums, 2048), (twGtwelfthW36pGT19Labs,
    twGtwelfthW36pGT19Nums, 2048), (twGtwelfthW36pGT20Labs, twGtwelfthW36pGT20Nums, 2048),
    (twGtwelfthW36pGT21Labs, twGtwelfthW36pGT21Nums, 2048), (twGtwelfthW36pGT22Labs,
    twGtwelfthW36pGT22Nums, 1704)] 3956736 = true := by
  decide +kernel

/-- The source short block as packed chunks. -/
theorem twGtwelfthW36p_Lsh : twGtwelfthW36pL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(twGtwelfthW36pHT0Labs, twGtwelfthW36pHT0Nums, 2048), (twGtwelfthW36pHT1Labs,
    twGtwelfthW36pHT1Nums, 2048), (twGtwelfthW36pHT2Labs, twGtwelfthW36pHT2Nums, 2048),
    (twGtwelfthW36pHT3Labs, twGtwelfthW36pHT3Nums, 2048), (twGtwelfthW36pHT4Labs,
    twGtwelfthW36pHT4Nums, 2048), (twGtwelfthW36pHT5Labs, twGtwelfthW36pHT5Nums, 2048),
    (twGtwelfthW36pHT6Labs, twGtwelfthW36pHT6Nums, 2048), (twGtwelfthW36pHT7Labs,
    twGtwelfthW36pHT7Nums, 2048), (twGtwelfthW36pHT8Labs, twGtwelfthW36pHT8Nums, 2048),
    (twGtwelfthW36pHT9Labs, twGtwelfthW36pHT9Nums, 2048), (twGtwelfthW36pHT10Labs,
    twGtwelfthW36pHT10Nums, 2048), (twGtwelfthW36pHT11Labs, twGtwelfthW36pHT11Nums, 2048),
    (twGtwelfthW36pHT12Labs, twGtwelfthW36pHT12Nums, 2048), (twGtwelfthW36pHT13Labs,
    twGtwelfthW36pHT13Nums, 2048), (twGtwelfthW36pHT14Labs, twGtwelfthW36pHT14Nums, 2048),
    (twGtwelfthW36pHT15Labs, twGtwelfthW36pHT15Nums, 2048), (twGtwelfthW36pHT16Labs,
    twGtwelfthW36pHT16Nums, 2048), (twGtwelfthW36pHT17Labs, twGtwelfthW36pHT17Nums, 2048),
    (twGtwelfthW36pHT18Labs, twGtwelfthW36pHT18Nums, 2048), (twGtwelfthW36pHT19Labs,
    twGtwelfthW36pHT19Nums, 2048), (twGtwelfthW36pHT20Labs, twGtwelfthW36pHT20Nums, 2048),
    (twGtwelfthW36pHT21Labs, twGtwelfthW36pHT21Nums, 2048), (twGtwelfthW36pHT22Labs,
    twGtwelfthW36pHT22Nums, 1704)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The target short block as packed chunks. -/
theorem twGtwelfthW36p_Wsh : twGtwelfthW36pW.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(twGtwelfthW36pGT0Labs, twGtwelfthW36pGT0Nums, 2048), (twGtwelfthW36pGT1Labs,
    twGtwelfthW36pGT1Nums, 2048), (twGtwelfthW36pGT2Labs, twGtwelfthW36pGT2Nums, 2048),
    (twGtwelfthW36pGT3Labs, twGtwelfthW36pGT3Nums, 2048), (twGtwelfthW36pGT4Labs,
    twGtwelfthW36pGT4Nums, 2048), (twGtwelfthW36pGT5Labs, twGtwelfthW36pGT5Nums, 2048),
    (twGtwelfthW36pGT6Labs, twGtwelfthW36pGT6Nums, 2048), (twGtwelfthW36pGT7Labs,
    twGtwelfthW36pGT7Nums, 2048), (twGtwelfthW36pGT8Labs, twGtwelfthW36pGT8Nums, 2048),
    (twGtwelfthW36pGT9Labs, twGtwelfthW36pGT9Nums, 2048), (twGtwelfthW36pGT10Labs,
    twGtwelfthW36pGT10Nums, 2048), (twGtwelfthW36pGT11Labs, twGtwelfthW36pGT11Nums, 2048),
    (twGtwelfthW36pGT12Labs, twGtwelfthW36pGT12Nums, 2048), (twGtwelfthW36pGT13Labs,
    twGtwelfthW36pGT13Nums, 2048), (twGtwelfthW36pGT14Labs, twGtwelfthW36pGT14Nums, 2048),
    (twGtwelfthW36pGT15Labs, twGtwelfthW36pGT15Nums, 2048), (twGtwelfthW36pGT16Labs,
    twGtwelfthW36pGT16Nums, 2048), (twGtwelfthW36pGT17Labs, twGtwelfthW36pGT17Nums, 2048),
    (twGtwelfthW36pGT18Labs, twGtwelfthW36pGT18Nums, 2048), (twGtwelfthW36pGT19Labs,
    twGtwelfthW36pGT19Nums, 2048), (twGtwelfthW36pGT20Labs, twGtwelfthW36pGT20Nums, 2048),
    (twGtwelfthW36pGT21Labs, twGtwelfthW36pGT21Nums, 2048), (twGtwelfthW36pGT22Labs,
    twGtwelfthW36pGT22Nums, 1704)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

/-- The octad terms of the source representation fit the packed octad transform. -/
theorem twGtwelfthW36p_hok : octPackOk 64 twGtwelfthW36pL = true :=
  OctadDense.octPackOk_of_chk 64 5 true twGtwelfthW36pL _ _ 3956736 twGtwelfthW36p_Lsh
      twGtwelfthW36p_chk

/-- The octad integer sum. -/
theorem twGtwelfthW36p_octn : octSumZ 64 true twGtwelfthW36pL twGtwelfthW36pW = 3956736 :=
  OctadDense.octSumZ_of_chk 64 5 true twGtwelfthW36pL twGtwelfthW36pW _ _ 3956736
      twGtwelfthW36p_Lsh twGtwelfthW36p_Wsh twGtwelfthW36p_chk

set_option maxRecDepth 100000 in
/-- The octad self sum of the target: one pass over its packed chunks (`selfOctChk`). -/
theorem twGtwelfthW36p_selfchk : OctadDense.selfOctChk 64 [(twGtwelfthW36pGT0Labs,
    twGtwelfthW36pGT0Nums, 2048), (twGtwelfthW36pGT1Labs, twGtwelfthW36pGT1Nums, 2048),
    (twGtwelfthW36pGT2Labs, twGtwelfthW36pGT2Nums, 2048), (twGtwelfthW36pGT3Labs,
    twGtwelfthW36pGT3Nums, 2048), (twGtwelfthW36pGT4Labs, twGtwelfthW36pGT4Nums, 2048),
    (twGtwelfthW36pGT5Labs, twGtwelfthW36pGT5Nums, 2048), (twGtwelfthW36pGT6Labs,
    twGtwelfthW36pGT6Nums, 2048), (twGtwelfthW36pGT7Labs, twGtwelfthW36pGT7Nums, 2048),
    (twGtwelfthW36pGT8Labs, twGtwelfthW36pGT8Nums, 2048), (twGtwelfthW36pGT9Labs,
    twGtwelfthW36pGT9Nums, 2048), (twGtwelfthW36pGT10Labs, twGtwelfthW36pGT10Nums, 2048),
    (twGtwelfthW36pGT11Labs, twGtwelfthW36pGT11Nums, 2048), (twGtwelfthW36pGT12Labs,
    twGtwelfthW36pGT12Nums, 2048), (twGtwelfthW36pGT13Labs, twGtwelfthW36pGT13Nums, 2048),
    (twGtwelfthW36pGT14Labs, twGtwelfthW36pGT14Nums, 2048), (twGtwelfthW36pGT15Labs,
    twGtwelfthW36pGT15Nums, 2048), (twGtwelfthW36pGT16Labs, twGtwelfthW36pGT16Nums, 2048),
    (twGtwelfthW36pGT17Labs, twGtwelfthW36pGT17Nums, 2048), (twGtwelfthW36pGT18Labs,
    twGtwelfthW36pGT18Nums, 2048), (twGtwelfthW36pGT19Labs, twGtwelfthW36pGT19Nums, 2048),
    (twGtwelfthW36pGT20Labs, twGtwelfthW36pGT20Nums, 2048), (twGtwelfthW36pGT21Labs,
    twGtwelfthW36pGT21Nums, 2048), (twGtwelfthW36pGT22Labs, twGtwelfthW36pGT22Nums, 1704)] 494592
    = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part equals the octad self part of the target. -/
theorem twGtwelfthW36p_hn : twGtwelfthW36pL.sden * (octSumZ 64 true twGtwelfthW36pL
    twGtwelfthW36pW : ℚ) / 8 =
    twGtwelfthW36pW.sden * (selfOctP twGtwelfthW36pW : ℚ) := by
  rw [twGtwelfthW36p_octn, selfOctP_eq, OctadDense.selfOctZ_of_chk 64 twGtwelfthW36pW _ 494592
      twGtwelfthW36p_Wsh twGtwelfthW36p_selfchk]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
