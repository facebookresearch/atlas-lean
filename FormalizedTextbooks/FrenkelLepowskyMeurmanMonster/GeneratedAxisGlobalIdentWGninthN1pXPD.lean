/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN1pXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN1pXTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (odd short terms) of the identification Ninth[1]+ <-> Twelfth[25]- (record
gninth:N1+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target short block as packed chunks, in groups. -/
theorem wGninthN1pX_WshG : wGninthN1pXW.sh = ShortData.ofList [OctadDense.octChunkTerms
    [(wGninthN1pXGT0Labs, wGninthN1pXGT0Nums, 2048), (wGninthN1pXGT1Labs, wGninthN1pXGT1Nums,
    2048), (wGninthN1pXGT2Labs, wGninthN1pXGT2Nums, 2048), (wGninthN1pXGT3Labs,
    wGninthN1pXGT3Nums, 2048)], OctadDense.octChunkTerms [(wGninthN1pXGT4Labs, wGninthN1pXGT4Nums,
    2048), (wGninthN1pXGT5Labs, wGninthN1pXGT5Nums, 2048), (wGninthN1pXGT6Labs,
    wGninthN1pXGT6Nums, 2048), (wGninthN1pXGT7Labs, wGninthN1pXGT7Nums, 2048)],
    OctadDense.octChunkTerms [(wGninthN1pXGT8Labs, wGninthN1pXGT8Nums, 2048), (wGninthN1pXGT9Labs,
    wGninthN1pXGT9Nums, 2048), (wGninthN1pXGT10Labs, wGninthN1pXGT10Nums, 2048),
    (wGninthN1pXGT11Labs, wGninthN1pXGT11Nums, 2048)], OctadDense.octChunkTerms
    [(wGninthN1pXGT12Labs, wGninthN1pXGT12Nums, 2048), (wGninthN1pXGT13Labs, wGninthN1pXGT13Nums,
    2048), (wGninthN1pXGT14Labs, wGninthN1pXGT14Nums, 2048), (wGninthN1pXGT15Labs,
    wGninthN1pXGT15Nums, 2048)], OctadDense.octChunkTerms [(wGninthN1pXGT16Labs,
    wGninthN1pXGT16Nums, 2048), (wGninthN1pXGT17Labs, wGninthN1pXGT17Nums, 2048),
    (wGninthN1pXGT18Labs, wGninthN1pXGT18Nums, 2048), (wGninthN1pXGT19Labs, wGninthN1pXGT19Nums,
    2048)], OctadDense.octChunkTerms [(wGninthN1pXGT20Labs, wGninthN1pXGT20Nums, 2048),
    (wGninthN1pXGT21Labs, wGninthN1pXGT21Nums, 2048), (wGninthN1pXGT22Labs, wGninthN1pXGT22Nums,
    1704)]].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, OctadDense.octChunkTerms,
    List.append_assoc]
  rfl

set_option maxRecDepth 100000 in
/-- The odd labels of the target are distinct. -/
theorem wGninthN1pX_sd : labDistinct wGninthN1pXW.sh.odd 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 0: equal to the odd self part of the group. -/
theorem wGninthN1pX_og0 : (oddSumF 64 true wGninthN1pXHX0 (OctadDense.octChunkTerms
    [(wGninthN1pXGT0Labs, wGninthN1pXGT0Nums, 2048), (wGninthN1pXGT1Labs, wGninthN1pXGT1Nums,
    2048), (wGninthN1pXGT2Labs, wGninthN1pXGT2Nums, 2048), (wGninthN1pXGT3Labs,
    wGninthN1pXGT3Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN1pXH : ℚ) * 32) / 2 ^ 4))
    =
    wGninthN1pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN1pXGT0Labs,
        wGninthN1pXGT0Nums, 2048), (wGninthN1pXGT1Labs, wGninthN1pXGT1Nums, 2048),
        (wGninthN1pXGT2Labs, wGninthN1pXGT2Nums, 2048), (wGninthN1pXGT3Labs, wGninthN1pXGT3Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 1: equal to the odd self part of the group. -/
theorem wGninthN1pX_og1 : (oddSumF 64 true wGninthN1pXHX0 (OctadDense.octChunkTerms
    [(wGninthN1pXGT4Labs, wGninthN1pXGT4Nums, 2048), (wGninthN1pXGT5Labs, wGninthN1pXGT5Nums,
    2048), (wGninthN1pXGT6Labs, wGninthN1pXGT6Nums, 2048), (wGninthN1pXGT7Labs,
    wGninthN1pXGT7Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN1pXH : ℚ) * 32) / 2 ^ 4))
    =
    wGninthN1pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN1pXGT4Labs,
        wGninthN1pXGT4Nums, 2048), (wGninthN1pXGT5Labs, wGninthN1pXGT5Nums, 2048),
        (wGninthN1pXGT6Labs, wGninthN1pXGT6Nums, 2048), (wGninthN1pXGT7Labs, wGninthN1pXGT7Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 2: equal to the odd self part of the group. -/
theorem wGninthN1pX_og2 : (oddSumF 64 true wGninthN1pXHX0 (OctadDense.octChunkTerms
    [(wGninthN1pXGT8Labs, wGninthN1pXGT8Nums, 2048), (wGninthN1pXGT9Labs, wGninthN1pXGT9Nums,
    2048), (wGninthN1pXGT10Labs, wGninthN1pXGT10Nums, 2048), (wGninthN1pXGT11Labs,
    wGninthN1pXGT11Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN1pXH : ℚ) * 32) / 2 ^ 4))
    =
    wGninthN1pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN1pXGT8Labs,
        wGninthN1pXGT8Nums, 2048), (wGninthN1pXGT9Labs, wGninthN1pXGT9Nums, 2048),
        (wGninthN1pXGT10Labs, wGninthN1pXGT10Nums, 2048), (wGninthN1pXGT11Labs,
        wGninthN1pXGT11Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 3: equal to the odd self part of the group. -/
theorem wGninthN1pX_og3 : (oddSumF 64 true wGninthN1pXHX0 (OctadDense.octChunkTerms
    [(wGninthN1pXGT12Labs, wGninthN1pXGT12Nums, 2048), (wGninthN1pXGT13Labs, wGninthN1pXGT13Nums,
    2048), (wGninthN1pXGT14Labs, wGninthN1pXGT14Nums, 2048), (wGninthN1pXGT15Labs,
    wGninthN1pXGT15Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN1pXH : ℚ) * 32) / 2 ^ 4))
    =
    wGninthN1pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN1pXGT12Labs,
        wGninthN1pXGT12Nums, 2048), (wGninthN1pXGT13Labs, wGninthN1pXGT13Nums, 2048),
        (wGninthN1pXGT14Labs, wGninthN1pXGT14Nums, 2048), (wGninthN1pXGT15Labs,
        wGninthN1pXGT15Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 4: equal to the odd self part of the group. -/
theorem wGninthN1pX_og4 : (oddSumF 64 true wGninthN1pXHX0 (OctadDense.octChunkTerms
    [(wGninthN1pXGT16Labs, wGninthN1pXGT16Nums, 2048), (wGninthN1pXGT17Labs, wGninthN1pXGT17Nums,
    2048), (wGninthN1pXGT18Labs, wGninthN1pXGT18Nums, 2048), (wGninthN1pXGT19Labs,
    wGninthN1pXGT19Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN1pXH : ℚ) * 32) / 2 ^ 4))
    =
    wGninthN1pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN1pXGT16Labs,
        wGninthN1pXGT16Nums, 2048), (wGninthN1pXGT17Labs, wGninthN1pXGT17Nums, 2048),
        (wGninthN1pXGT18Labs, wGninthN1pXGT18Nums, 2048), (wGninthN1pXGT19Labs,
        wGninthN1pXGT19Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 5: equal to the odd self part of the group. -/
theorem wGninthN1pX_og5 : (oddSumF 64 true wGninthN1pXHX0 (OctadDense.octChunkTerms
    [(wGninthN1pXGT20Labs, wGninthN1pXGT20Nums, 2048), (wGninthN1pXGT21Labs, wGninthN1pXGT21Nums,
    2048), (wGninthN1pXGT22Labs, wGninthN1pXGT22Nums, 1704)]) : ℚ) / (2 * (((tensorWordDenAll
    wGninthN1pXH : ℚ) * 32) / 2 ^ 4)) =
    wGninthN1pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN1pXGT20Labs,
        wGninthN1pXGT20Nums, 2048), (wGninthN1pXGT21Labs, wGninthN1pXGT21Nums, 2048),
        (wGninthN1pXGT22Labs, wGninthN1pXGT22Nums, 1704)])) : ℚ) := by
  decide +kernel

/-- The odd short part equals the odd self part of the target (group checks, no predicted values).
-/
theorem wGninthN1pX_ha : (oddWZ 64 true wGninthN1pXHX0 wGninthN1pXW : ℚ) / (2 *
    (((tensorWordDenAll wGninthN1pXH : ℚ) * 32) / 2 ^ 4)) =
    wGninthN1pXW.sden * (selfOddP wGninthN1pXW : ℚ) :=
  oddPart_of_groups 64 true wGninthN1pXHX0 wGninthN1pXW _ wGninthN1pX_WshG wGninthN1pX_sd
      (((tensorWordDenAll wGninthN1pXH : ℚ) * 32) / 2 ^ 4) (by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [wGninthN1pX_og0, wGninthN1pX_og1, wGninthN1pX_og2, wGninthN1pX_og3, wGninthN1pX_og4,
        wGninthN1pX_og5])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
