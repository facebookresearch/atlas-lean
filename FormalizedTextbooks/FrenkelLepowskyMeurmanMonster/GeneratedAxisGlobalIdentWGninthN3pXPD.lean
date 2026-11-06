/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN3pXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN3pXTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (odd short terms) of the identification Ninth[5]+ <-> Twelfth[31]+ (record
gninth:N3+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target short block as packed chunks, in groups. -/
theorem wGninthN3pX_WshG : wGninthN3pXW.sh = ShortData.ofList [OctadDense.octChunkTerms
    [(wGninthN3pXGT0Labs, wGninthN3pXGT0Nums, 2048), (wGninthN3pXGT1Labs, wGninthN3pXGT1Nums,
    2048), (wGninthN3pXGT2Labs, wGninthN3pXGT2Nums, 2048), (wGninthN3pXGT3Labs,
    wGninthN3pXGT3Nums, 2048)], OctadDense.octChunkTerms [(wGninthN3pXGT4Labs, wGninthN3pXGT4Nums,
    2048), (wGninthN3pXGT5Labs, wGninthN3pXGT5Nums, 2048), (wGninthN3pXGT6Labs,
    wGninthN3pXGT6Nums, 2048), (wGninthN3pXGT7Labs, wGninthN3pXGT7Nums, 2048)],
    OctadDense.octChunkTerms [(wGninthN3pXGT8Labs, wGninthN3pXGT8Nums, 2048), (wGninthN3pXGT9Labs,
    wGninthN3pXGT9Nums, 2048), (wGninthN3pXGT10Labs, wGninthN3pXGT10Nums, 2048),
    (wGninthN3pXGT11Labs, wGninthN3pXGT11Nums, 2048)], OctadDense.octChunkTerms
    [(wGninthN3pXGT12Labs, wGninthN3pXGT12Nums, 2048), (wGninthN3pXGT13Labs, wGninthN3pXGT13Nums,
    2048), (wGninthN3pXGT14Labs, wGninthN3pXGT14Nums, 2048), (wGninthN3pXGT15Labs,
    wGninthN3pXGT15Nums, 2048)], OctadDense.octChunkTerms [(wGninthN3pXGT16Labs,
    wGninthN3pXGT16Nums, 2048), (wGninthN3pXGT17Labs, wGninthN3pXGT17Nums, 2048),
    (wGninthN3pXGT18Labs, wGninthN3pXGT18Nums, 2048), (wGninthN3pXGT19Labs, wGninthN3pXGT19Nums,
    2048)], OctadDense.octChunkTerms [(wGninthN3pXGT20Labs, wGninthN3pXGT20Nums, 2048),
    (wGninthN3pXGT21Labs, wGninthN3pXGT21Nums, 2048), (wGninthN3pXGT22Labs, wGninthN3pXGT22Nums,
    1704)]].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, OctadDense.octChunkTerms,
    List.append_assoc]
  rfl

set_option maxRecDepth 100000 in
/-- The odd labels of the target are distinct. -/
theorem wGninthN3pX_sd : labDistinct wGninthN3pXW.sh.odd 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 0: equal to the odd self part of the group. -/
theorem wGninthN3pX_og0 : (oddSumF 64 true wGninthN3pXHX0 (OctadDense.octChunkTerms
    [(wGninthN3pXGT0Labs, wGninthN3pXGT0Nums, 2048), (wGninthN3pXGT1Labs, wGninthN3pXGT1Nums,
    2048), (wGninthN3pXGT2Labs, wGninthN3pXGT2Nums, 2048), (wGninthN3pXGT3Labs,
    wGninthN3pXGT3Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN3pXH : ℚ) * 32) / 2 ^ 4))
    =
    wGninthN3pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN3pXGT0Labs,
        wGninthN3pXGT0Nums, 2048), (wGninthN3pXGT1Labs, wGninthN3pXGT1Nums, 2048),
        (wGninthN3pXGT2Labs, wGninthN3pXGT2Nums, 2048), (wGninthN3pXGT3Labs, wGninthN3pXGT3Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 1: equal to the odd self part of the group. -/
theorem wGninthN3pX_og1 : (oddSumF 64 true wGninthN3pXHX0 (OctadDense.octChunkTerms
    [(wGninthN3pXGT4Labs, wGninthN3pXGT4Nums, 2048), (wGninthN3pXGT5Labs, wGninthN3pXGT5Nums,
    2048), (wGninthN3pXGT6Labs, wGninthN3pXGT6Nums, 2048), (wGninthN3pXGT7Labs,
    wGninthN3pXGT7Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN3pXH : ℚ) * 32) / 2 ^ 4))
    =
    wGninthN3pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN3pXGT4Labs,
        wGninthN3pXGT4Nums, 2048), (wGninthN3pXGT5Labs, wGninthN3pXGT5Nums, 2048),
        (wGninthN3pXGT6Labs, wGninthN3pXGT6Nums, 2048), (wGninthN3pXGT7Labs, wGninthN3pXGT7Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 2: equal to the odd self part of the group. -/
theorem wGninthN3pX_og2 : (oddSumF 64 true wGninthN3pXHX0 (OctadDense.octChunkTerms
    [(wGninthN3pXGT8Labs, wGninthN3pXGT8Nums, 2048), (wGninthN3pXGT9Labs, wGninthN3pXGT9Nums,
    2048), (wGninthN3pXGT10Labs, wGninthN3pXGT10Nums, 2048), (wGninthN3pXGT11Labs,
    wGninthN3pXGT11Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN3pXH : ℚ) * 32) / 2 ^ 4))
    =
    wGninthN3pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN3pXGT8Labs,
        wGninthN3pXGT8Nums, 2048), (wGninthN3pXGT9Labs, wGninthN3pXGT9Nums, 2048),
        (wGninthN3pXGT10Labs, wGninthN3pXGT10Nums, 2048), (wGninthN3pXGT11Labs,
        wGninthN3pXGT11Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 3: equal to the odd self part of the group. -/
theorem wGninthN3pX_og3 : (oddSumF 64 true wGninthN3pXHX0 (OctadDense.octChunkTerms
    [(wGninthN3pXGT12Labs, wGninthN3pXGT12Nums, 2048), (wGninthN3pXGT13Labs, wGninthN3pXGT13Nums,
    2048), (wGninthN3pXGT14Labs, wGninthN3pXGT14Nums, 2048), (wGninthN3pXGT15Labs,
    wGninthN3pXGT15Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN3pXH : ℚ) * 32) / 2 ^ 4))
    =
    wGninthN3pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN3pXGT12Labs,
        wGninthN3pXGT12Nums, 2048), (wGninthN3pXGT13Labs, wGninthN3pXGT13Nums, 2048),
        (wGninthN3pXGT14Labs, wGninthN3pXGT14Nums, 2048), (wGninthN3pXGT15Labs,
        wGninthN3pXGT15Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 4: equal to the odd self part of the group. -/
theorem wGninthN3pX_og4 : (oddSumF 64 true wGninthN3pXHX0 (OctadDense.octChunkTerms
    [(wGninthN3pXGT16Labs, wGninthN3pXGT16Nums, 2048), (wGninthN3pXGT17Labs, wGninthN3pXGT17Nums,
    2048), (wGninthN3pXGT18Labs, wGninthN3pXGT18Nums, 2048), (wGninthN3pXGT19Labs,
    wGninthN3pXGT19Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN3pXH : ℚ) * 32) / 2 ^ 4))
    =
    wGninthN3pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN3pXGT16Labs,
        wGninthN3pXGT16Nums, 2048), (wGninthN3pXGT17Labs, wGninthN3pXGT17Nums, 2048),
        (wGninthN3pXGT18Labs, wGninthN3pXGT18Nums, 2048), (wGninthN3pXGT19Labs,
        wGninthN3pXGT19Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 5: equal to the odd self part of the group. -/
theorem wGninthN3pX_og5 : (oddSumF 64 true wGninthN3pXHX0 (OctadDense.octChunkTerms
    [(wGninthN3pXGT20Labs, wGninthN3pXGT20Nums, 2048), (wGninthN3pXGT21Labs, wGninthN3pXGT21Nums,
    2048), (wGninthN3pXGT22Labs, wGninthN3pXGT22Nums, 1704)]) : ℚ) / (2 * (((tensorWordDenAll
    wGninthN3pXH : ℚ) * 32) / 2 ^ 4)) =
    wGninthN3pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN3pXGT20Labs,
        wGninthN3pXGT20Nums, 2048), (wGninthN3pXGT21Labs, wGninthN3pXGT21Nums, 2048),
        (wGninthN3pXGT22Labs, wGninthN3pXGT22Nums, 1704)])) : ℚ) := by
  decide +kernel

/-- The odd short part equals the odd self part of the target (group checks, no predicted values).
-/
theorem wGninthN3pX_ha : (oddWZ 64 true wGninthN3pXHX0 wGninthN3pXW : ℚ) / (2 *
    (((tensorWordDenAll wGninthN3pXH : ℚ) * 32) / 2 ^ 4)) =
    wGninthN3pXW.sden * (selfOddP wGninthN3pXW : ℚ) :=
  oddPart_of_groups 64 true wGninthN3pXHX0 wGninthN3pXW _ wGninthN3pX_WshG wGninthN3pX_sd
      (((tensorWordDenAll wGninthN3pXH : ℚ) * 32) / 2 ^ 4) (by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [wGninthN3pX_og0, wGninthN3pX_og1, wGninthN3pX_og2, wGninthN3pX_og3, wGninthN3pX_og4,
        wGninthN3pX_og5])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
