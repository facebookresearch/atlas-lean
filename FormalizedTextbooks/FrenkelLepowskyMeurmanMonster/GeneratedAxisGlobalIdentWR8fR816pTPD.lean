/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR816pTChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR816pTTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (odd short terms) of the identification Root8[22]+ <-> Root8[22]+ (record
r8f:R816+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target short block as packed chunks, in groups. -/
theorem wR8fR816pT_WshG : wR8fR816pTW.sh = ShortData.ofList [OctadDense.octChunkTerms
    [(wR8fR816pTGT0Labs, wR8fR816pTGT0Nums, 2048), (wR8fR816pTGT1Labs, wR8fR816pTGT1Nums, 2048),
    (wR8fR816pTGT2Labs, wR8fR816pTGT2Nums, 2048), (wR8fR816pTGT3Labs, wR8fR816pTGT3Nums, 2048)],
    OctadDense.octChunkTerms [(wR8fR816pTGT4Labs, wR8fR816pTGT4Nums, 2048), (wR8fR816pTGT5Labs,
    wR8fR816pTGT5Nums, 2048), (wR8fR816pTGT6Labs, wR8fR816pTGT6Nums, 2048), (wR8fR816pTGT7Labs,
    wR8fR816pTGT7Nums, 2048)], OctadDense.octChunkTerms [(wR8fR816pTGT8Labs, wR8fR816pTGT8Nums,
    2048), (wR8fR816pTGT9Labs, wR8fR816pTGT9Nums, 2048), (wR8fR816pTGT10Labs, wR8fR816pTGT10Nums,
    2048), (wR8fR816pTGT11Labs, wR8fR816pTGT11Nums, 2048)], OctadDense.octChunkTerms
    [(wR8fR816pTGT12Labs, wR8fR816pTGT12Nums, 2048), (wR8fR816pTGT13Labs, wR8fR816pTGT13Nums,
    2048), (wR8fR816pTGT14Labs, wR8fR816pTGT14Nums, 2048), (wR8fR816pTGT15Labs,
    wR8fR816pTGT15Nums, 2048)], OctadDense.octChunkTerms [(wR8fR816pTGT16Labs, wR8fR816pTGT16Nums,
    808)]].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, OctadDense.octChunkTerms,
    List.append_assoc]
  rfl

set_option maxRecDepth 100000 in
/-- The odd labels of the target are distinct. -/
theorem wR8fR816pT_sd : labDistinct wR8fR816pTW.sh.odd 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 0: equal to the odd self part of the group. -/
theorem wR8fR816pT_og0 : (oddSumF 64 true wR8fR816pTHX0 (OctadDense.octChunkTerms
    [(wR8fR816pTGT0Labs, wR8fR816pTGT0Nums, 2048), (wR8fR816pTGT1Labs, wR8fR816pTGT1Nums, 2048),
    (wR8fR816pTGT2Labs, wR8fR816pTGT2Nums, 2048), (wR8fR816pTGT3Labs, wR8fR816pTGT3Nums, 2048)]) :
    ℚ) / (2 * (((tensorWordDenAll wR8fR816pTH : ℚ) * 32) / 2 ^ 20)) =
    wR8fR816pTW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wR8fR816pTGT0Labs,
        wR8fR816pTGT0Nums, 2048), (wR8fR816pTGT1Labs, wR8fR816pTGT1Nums, 2048),
        (wR8fR816pTGT2Labs, wR8fR816pTGT2Nums, 2048), (wR8fR816pTGT3Labs, wR8fR816pTGT3Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 1: equal to the odd self part of the group. -/
theorem wR8fR816pT_og1 : (oddSumF 64 true wR8fR816pTHX0 (OctadDense.octChunkTerms
    [(wR8fR816pTGT4Labs, wR8fR816pTGT4Nums, 2048), (wR8fR816pTGT5Labs, wR8fR816pTGT5Nums, 2048),
    (wR8fR816pTGT6Labs, wR8fR816pTGT6Nums, 2048), (wR8fR816pTGT7Labs, wR8fR816pTGT7Nums, 2048)]) :
    ℚ) / (2 * (((tensorWordDenAll wR8fR816pTH : ℚ) * 32) / 2 ^ 20)) =
    wR8fR816pTW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wR8fR816pTGT4Labs,
        wR8fR816pTGT4Nums, 2048), (wR8fR816pTGT5Labs, wR8fR816pTGT5Nums, 2048),
        (wR8fR816pTGT6Labs, wR8fR816pTGT6Nums, 2048), (wR8fR816pTGT7Labs, wR8fR816pTGT7Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 2: equal to the odd self part of the group. -/
theorem wR8fR816pT_og2 : (oddSumF 64 true wR8fR816pTHX0 (OctadDense.octChunkTerms
    [(wR8fR816pTGT8Labs, wR8fR816pTGT8Nums, 2048), (wR8fR816pTGT9Labs, wR8fR816pTGT9Nums, 2048),
    (wR8fR816pTGT10Labs, wR8fR816pTGT10Nums, 2048), (wR8fR816pTGT11Labs, wR8fR816pTGT11Nums,
    2048)]) : ℚ) / (2 * (((tensorWordDenAll wR8fR816pTH : ℚ) * 32) / 2 ^ 20)) =
    wR8fR816pTW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wR8fR816pTGT8Labs,
        wR8fR816pTGT8Nums, 2048), (wR8fR816pTGT9Labs, wR8fR816pTGT9Nums, 2048),
        (wR8fR816pTGT10Labs, wR8fR816pTGT10Nums, 2048), (wR8fR816pTGT11Labs, wR8fR816pTGT11Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 3: equal to the odd self part of the group. -/
theorem wR8fR816pT_og3 : (oddSumF 64 true wR8fR816pTHX0 (OctadDense.octChunkTerms
    [(wR8fR816pTGT12Labs, wR8fR816pTGT12Nums, 2048), (wR8fR816pTGT13Labs, wR8fR816pTGT13Nums,
    2048), (wR8fR816pTGT14Labs, wR8fR816pTGT14Nums, 2048), (wR8fR816pTGT15Labs,
    wR8fR816pTGT15Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wR8fR816pTH : ℚ) * 32) / 2 ^ 20))
    =
    wR8fR816pTW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wR8fR816pTGT12Labs,
        wR8fR816pTGT12Nums, 2048), (wR8fR816pTGT13Labs, wR8fR816pTGT13Nums, 2048),
        (wR8fR816pTGT14Labs, wR8fR816pTGT14Nums, 2048), (wR8fR816pTGT15Labs, wR8fR816pTGT15Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 4: equal to the odd self part of the group. -/
theorem wR8fR816pT_og4 : (oddSumF 64 true wR8fR816pTHX0 (OctadDense.octChunkTerms
    [(wR8fR816pTGT16Labs, wR8fR816pTGT16Nums, 808)]) : ℚ) / (2 * (((tensorWordDenAll wR8fR816pTH :
    ℚ) * 32) / 2 ^ 20)) =
    wR8fR816pTW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wR8fR816pTGT16Labs,
        wR8fR816pTGT16Nums, 808)])) : ℚ) := by
  decide +kernel

/-- The odd short part equals the odd self part of the target (group checks, no predicted values).
-/
theorem wR8fR816pT_ha : (oddWZ 64 true wR8fR816pTHX0 wR8fR816pTW : ℚ) / (2 * (((tensorWordDenAll
    wR8fR816pTH : ℚ) * 32) / 2 ^ 20)) =
    wR8fR816pTW.sden * (selfOddP wR8fR816pTW : ℚ) :=
  oddPart_of_groups 64 true wR8fR816pTHX0 wR8fR816pTW _ wR8fR816pT_WshG wR8fR816pT_sd
      (((tensorWordDenAll wR8fR816pTH : ℚ) * 32) / 2 ^ 20) (by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl
    exacts [wR8fR816pT_og0, wR8fR816pT_og1, wR8fR816pT_og2, wR8fR816pT_og3, wR8fR816pT_og4])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
