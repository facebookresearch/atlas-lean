/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN6pXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN6pXTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (odd short terms) of the identification Ninth[10]+ <-> Twelfth[12]- (record
gninth:N6+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target short block as packed chunks, in groups. -/
theorem wGninthN6pX_WshG : wGninthN6pXW.sh = ShortData.ofList [OctadDense.octChunkTerms
    [(wGninthN6pXGT0Labs, wGninthN6pXGT0Nums, 2048), (wGninthN6pXGT1Labs, wGninthN6pXGT1Nums,
    2048), (wGninthN6pXGT2Labs, wGninthN6pXGT2Nums, 2048), (wGninthN6pXGT3Labs,
    wGninthN6pXGT3Nums, 2048)], OctadDense.octChunkTerms [(wGninthN6pXGT4Labs, wGninthN6pXGT4Nums,
    2048), (wGninthN6pXGT5Labs, wGninthN6pXGT5Nums, 2048), (wGninthN6pXGT6Labs,
    wGninthN6pXGT6Nums, 2048), (wGninthN6pXGT7Labs, wGninthN6pXGT7Nums, 2048)],
    OctadDense.octChunkTerms [(wGninthN6pXGT8Labs, wGninthN6pXGT8Nums, 2048), (wGninthN6pXGT9Labs,
    wGninthN6pXGT9Nums, 2048), (wGninthN6pXGT10Labs, wGninthN6pXGT10Nums, 2048),
    (wGninthN6pXGT11Labs, wGninthN6pXGT11Nums, 2048)], OctadDense.octChunkTerms
    [(wGninthN6pXGT12Labs, wGninthN6pXGT12Nums, 2048), (wGninthN6pXGT13Labs, wGninthN6pXGT13Nums,
    2048), (wGninthN6pXGT14Labs, wGninthN6pXGT14Nums, 2048), (wGninthN6pXGT15Labs,
    wGninthN6pXGT15Nums, 2048)], OctadDense.octChunkTerms [(wGninthN6pXGT16Labs,
    wGninthN6pXGT16Nums, 2048), (wGninthN6pXGT17Labs, wGninthN6pXGT17Nums, 2048),
    (wGninthN6pXGT18Labs, wGninthN6pXGT18Nums, 2048), (wGninthN6pXGT19Labs, wGninthN6pXGT19Nums,
    2048)], OctadDense.octChunkTerms [(wGninthN6pXGT20Labs, wGninthN6pXGT20Nums, 2048),
    (wGninthN6pXGT21Labs, wGninthN6pXGT21Nums, 2048), (wGninthN6pXGT22Labs, wGninthN6pXGT22Nums,
    1704)]].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, OctadDense.octChunkTerms,
    List.append_assoc]
  rfl

set_option maxRecDepth 100000 in
/-- The odd labels of the target are distinct. -/
theorem wGninthN6pX_sd : labDistinct wGninthN6pXW.sh.odd 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 0: equal to the odd self part of the group. -/
theorem wGninthN6pX_og0 : (oddSumF 64 true wGninthN6pXHX0 (OctadDense.octChunkTerms
    [(wGninthN6pXGT0Labs, wGninthN6pXGT0Nums, 2048), (wGninthN6pXGT1Labs, wGninthN6pXGT1Nums,
    2048), (wGninthN6pXGT2Labs, wGninthN6pXGT2Nums, 2048), (wGninthN6pXGT3Labs,
    wGninthN6pXGT3Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN6pXH : ℚ) * 32) / 2 ^ 16))
    =
    wGninthN6pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN6pXGT0Labs,
        wGninthN6pXGT0Nums, 2048), (wGninthN6pXGT1Labs, wGninthN6pXGT1Nums, 2048),
        (wGninthN6pXGT2Labs, wGninthN6pXGT2Nums, 2048), (wGninthN6pXGT3Labs, wGninthN6pXGT3Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 1: equal to the odd self part of the group. -/
theorem wGninthN6pX_og1 : (oddSumF 64 true wGninthN6pXHX0 (OctadDense.octChunkTerms
    [(wGninthN6pXGT4Labs, wGninthN6pXGT4Nums, 2048), (wGninthN6pXGT5Labs, wGninthN6pXGT5Nums,
    2048), (wGninthN6pXGT6Labs, wGninthN6pXGT6Nums, 2048), (wGninthN6pXGT7Labs,
    wGninthN6pXGT7Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN6pXH : ℚ) * 32) / 2 ^ 16))
    =
    wGninthN6pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN6pXGT4Labs,
        wGninthN6pXGT4Nums, 2048), (wGninthN6pXGT5Labs, wGninthN6pXGT5Nums, 2048),
        (wGninthN6pXGT6Labs, wGninthN6pXGT6Nums, 2048), (wGninthN6pXGT7Labs, wGninthN6pXGT7Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 2: equal to the odd self part of the group. -/
theorem wGninthN6pX_og2 : (oddSumF 64 true wGninthN6pXHX0 (OctadDense.octChunkTerms
    [(wGninthN6pXGT8Labs, wGninthN6pXGT8Nums, 2048), (wGninthN6pXGT9Labs, wGninthN6pXGT9Nums,
    2048), (wGninthN6pXGT10Labs, wGninthN6pXGT10Nums, 2048), (wGninthN6pXGT11Labs,
    wGninthN6pXGT11Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN6pXH : ℚ) * 32) / 2 ^
    16)) =
    wGninthN6pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN6pXGT8Labs,
        wGninthN6pXGT8Nums, 2048), (wGninthN6pXGT9Labs, wGninthN6pXGT9Nums, 2048),
        (wGninthN6pXGT10Labs, wGninthN6pXGT10Nums, 2048), (wGninthN6pXGT11Labs,
        wGninthN6pXGT11Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 3: equal to the odd self part of the group. -/
theorem wGninthN6pX_og3 : (oddSumF 64 true wGninthN6pXHX0 (OctadDense.octChunkTerms
    [(wGninthN6pXGT12Labs, wGninthN6pXGT12Nums, 2048), (wGninthN6pXGT13Labs, wGninthN6pXGT13Nums,
    2048), (wGninthN6pXGT14Labs, wGninthN6pXGT14Nums, 2048), (wGninthN6pXGT15Labs,
    wGninthN6pXGT15Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN6pXH : ℚ) * 32) / 2 ^
    16)) =
    wGninthN6pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN6pXGT12Labs,
        wGninthN6pXGT12Nums, 2048), (wGninthN6pXGT13Labs, wGninthN6pXGT13Nums, 2048),
        (wGninthN6pXGT14Labs, wGninthN6pXGT14Nums, 2048), (wGninthN6pXGT15Labs,
        wGninthN6pXGT15Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 4: equal to the odd self part of the group. -/
theorem wGninthN6pX_og4 : (oddSumF 64 true wGninthN6pXHX0 (OctadDense.octChunkTerms
    [(wGninthN6pXGT16Labs, wGninthN6pXGT16Nums, 2048), (wGninthN6pXGT17Labs, wGninthN6pXGT17Nums,
    2048), (wGninthN6pXGT18Labs, wGninthN6pXGT18Nums, 2048), (wGninthN6pXGT19Labs,
    wGninthN6pXGT19Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN6pXH : ℚ) * 32) / 2 ^
    16)) =
    wGninthN6pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN6pXGT16Labs,
        wGninthN6pXGT16Nums, 2048), (wGninthN6pXGT17Labs, wGninthN6pXGT17Nums, 2048),
        (wGninthN6pXGT18Labs, wGninthN6pXGT18Nums, 2048), (wGninthN6pXGT19Labs,
        wGninthN6pXGT19Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 5: equal to the odd self part of the group. -/
theorem wGninthN6pX_og5 : (oddSumF 64 true wGninthN6pXHX0 (OctadDense.octChunkTerms
    [(wGninthN6pXGT20Labs, wGninthN6pXGT20Nums, 2048), (wGninthN6pXGT21Labs, wGninthN6pXGT21Nums,
    2048), (wGninthN6pXGT22Labs, wGninthN6pXGT22Nums, 1704)]) : ℚ) / (2 * (((tensorWordDenAll
    wGninthN6pXH : ℚ) * 32) / 2 ^ 16)) =
    wGninthN6pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN6pXGT20Labs,
        wGninthN6pXGT20Nums, 2048), (wGninthN6pXGT21Labs, wGninthN6pXGT21Nums, 2048),
        (wGninthN6pXGT22Labs, wGninthN6pXGT22Nums, 1704)])) : ℚ) := by
  decide +kernel

/-- The odd short part equals the odd self part of the target (group checks, no predicted values).
-/
theorem wGninthN6pX_ha : (oddWZ 64 true wGninthN6pXHX0 wGninthN6pXW : ℚ) / (2 *
    (((tensorWordDenAll wGninthN6pXH : ℚ) * 32) / 2 ^ 16)) =
    wGninthN6pXW.sden * (selfOddP wGninthN6pXW : ℚ) :=
  oddPart_of_groups 64 true wGninthN6pXHX0 wGninthN6pXW _ wGninthN6pX_WshG wGninthN6pX_sd
      (((tensorWordDenAll wGninthN6pXH : ℚ) * 32) / 2 ^ 16) (by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [wGninthN6pX_og0, wGninthN6pX_og1, wGninthN6pX_og2, wGninthN6pX_og3, wGninthN6pX_og4,
        wGninthN6pX_og5])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
