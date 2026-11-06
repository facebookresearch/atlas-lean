/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN3nXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN3nXTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (odd short terms) of the identification Ninth[5]- <-> Twelfth[31]+ (record
gninth:N3-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target short block as packed chunks, in groups. -/
theorem wGninthN3nX_WshG : wGninthN3nXW.sh = ShortData.ofList [OctadDense.octChunkTerms
    [(wGninthN3nXGT0Labs, wGninthN3nXGT0Nums, 2048), (wGninthN3nXGT1Labs, wGninthN3nXGT1Nums,
    2048), (wGninthN3nXGT2Labs, wGninthN3nXGT2Nums, 2048), (wGninthN3nXGT3Labs,
    wGninthN3nXGT3Nums, 2048)], OctadDense.octChunkTerms [(wGninthN3nXGT4Labs, wGninthN3nXGT4Nums,
    2048), (wGninthN3nXGT5Labs, wGninthN3nXGT5Nums, 2048), (wGninthN3nXGT6Labs,
    wGninthN3nXGT6Nums, 2048), (wGninthN3nXGT7Labs, wGninthN3nXGT7Nums, 2048)],
    OctadDense.octChunkTerms [(wGninthN3nXGT8Labs, wGninthN3nXGT8Nums, 2048), (wGninthN3nXGT9Labs,
    wGninthN3nXGT9Nums, 2048), (wGninthN3nXGT10Labs, wGninthN3nXGT10Nums, 2048),
    (wGninthN3nXGT11Labs, wGninthN3nXGT11Nums, 2048)], OctadDense.octChunkTerms
    [(wGninthN3nXGT12Labs, wGninthN3nXGT12Nums, 2048), (wGninthN3nXGT13Labs, wGninthN3nXGT13Nums,
    2048), (wGninthN3nXGT14Labs, wGninthN3nXGT14Nums, 2048), (wGninthN3nXGT15Labs,
    wGninthN3nXGT15Nums, 2048)], OctadDense.octChunkTerms [(wGninthN3nXGT16Labs,
    wGninthN3nXGT16Nums, 2048), (wGninthN3nXGT17Labs, wGninthN3nXGT17Nums, 2048),
    (wGninthN3nXGT18Labs, wGninthN3nXGT18Nums, 2048), (wGninthN3nXGT19Labs, wGninthN3nXGT19Nums,
    2048)], OctadDense.octChunkTerms [(wGninthN3nXGT20Labs, wGninthN3nXGT20Nums, 2048),
    (wGninthN3nXGT21Labs, wGninthN3nXGT21Nums, 2048), (wGninthN3nXGT22Labs, wGninthN3nXGT22Nums,
    1704)]].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, OctadDense.octChunkTerms,
    List.append_assoc]
  rfl

set_option maxRecDepth 100000 in
/-- The odd labels of the target are distinct. -/
theorem wGninthN3nX_sd : labDistinct wGninthN3nXW.sh.odd 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 0: equal to the odd self part of the group. -/
theorem wGninthN3nX_og0 : (oddSumF 64 false wGninthN3nXHX0 (OctadDense.octChunkTerms
    [(wGninthN3nXGT0Labs, wGninthN3nXGT0Nums, 2048), (wGninthN3nXGT1Labs, wGninthN3nXGT1Nums,
    2048), (wGninthN3nXGT2Labs, wGninthN3nXGT2Nums, 2048), (wGninthN3nXGT3Labs,
    wGninthN3nXGT3Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN3nXH : ℚ) * 32) / 2 ^ 4))
    =
    wGninthN3nXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN3nXGT0Labs,
        wGninthN3nXGT0Nums, 2048), (wGninthN3nXGT1Labs, wGninthN3nXGT1Nums, 2048),
        (wGninthN3nXGT2Labs, wGninthN3nXGT2Nums, 2048), (wGninthN3nXGT3Labs, wGninthN3nXGT3Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 1: equal to the odd self part of the group. -/
theorem wGninthN3nX_og1 : (oddSumF 64 false wGninthN3nXHX0 (OctadDense.octChunkTerms
    [(wGninthN3nXGT4Labs, wGninthN3nXGT4Nums, 2048), (wGninthN3nXGT5Labs, wGninthN3nXGT5Nums,
    2048), (wGninthN3nXGT6Labs, wGninthN3nXGT6Nums, 2048), (wGninthN3nXGT7Labs,
    wGninthN3nXGT7Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN3nXH : ℚ) * 32) / 2 ^ 4))
    =
    wGninthN3nXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN3nXGT4Labs,
        wGninthN3nXGT4Nums, 2048), (wGninthN3nXGT5Labs, wGninthN3nXGT5Nums, 2048),
        (wGninthN3nXGT6Labs, wGninthN3nXGT6Nums, 2048), (wGninthN3nXGT7Labs, wGninthN3nXGT7Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 2: equal to the odd self part of the group. -/
theorem wGninthN3nX_og2 : (oddSumF 64 false wGninthN3nXHX0 (OctadDense.octChunkTerms
    [(wGninthN3nXGT8Labs, wGninthN3nXGT8Nums, 2048), (wGninthN3nXGT9Labs, wGninthN3nXGT9Nums,
    2048), (wGninthN3nXGT10Labs, wGninthN3nXGT10Nums, 2048), (wGninthN3nXGT11Labs,
    wGninthN3nXGT11Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN3nXH : ℚ) * 32) / 2 ^ 4))
    =
    wGninthN3nXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN3nXGT8Labs,
        wGninthN3nXGT8Nums, 2048), (wGninthN3nXGT9Labs, wGninthN3nXGT9Nums, 2048),
        (wGninthN3nXGT10Labs, wGninthN3nXGT10Nums, 2048), (wGninthN3nXGT11Labs,
        wGninthN3nXGT11Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 3: equal to the odd self part of the group. -/
theorem wGninthN3nX_og3 : (oddSumF 64 false wGninthN3nXHX0 (OctadDense.octChunkTerms
    [(wGninthN3nXGT12Labs, wGninthN3nXGT12Nums, 2048), (wGninthN3nXGT13Labs, wGninthN3nXGT13Nums,
    2048), (wGninthN3nXGT14Labs, wGninthN3nXGT14Nums, 2048), (wGninthN3nXGT15Labs,
    wGninthN3nXGT15Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN3nXH : ℚ) * 32) / 2 ^ 4))
    =
    wGninthN3nXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN3nXGT12Labs,
        wGninthN3nXGT12Nums, 2048), (wGninthN3nXGT13Labs, wGninthN3nXGT13Nums, 2048),
        (wGninthN3nXGT14Labs, wGninthN3nXGT14Nums, 2048), (wGninthN3nXGT15Labs,
        wGninthN3nXGT15Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 4: equal to the odd self part of the group. -/
theorem wGninthN3nX_og4 : (oddSumF 64 false wGninthN3nXHX0 (OctadDense.octChunkTerms
    [(wGninthN3nXGT16Labs, wGninthN3nXGT16Nums, 2048), (wGninthN3nXGT17Labs, wGninthN3nXGT17Nums,
    2048), (wGninthN3nXGT18Labs, wGninthN3nXGT18Nums, 2048), (wGninthN3nXGT19Labs,
    wGninthN3nXGT19Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN3nXH : ℚ) * 32) / 2 ^ 4))
    =
    wGninthN3nXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN3nXGT16Labs,
        wGninthN3nXGT16Nums, 2048), (wGninthN3nXGT17Labs, wGninthN3nXGT17Nums, 2048),
        (wGninthN3nXGT18Labs, wGninthN3nXGT18Nums, 2048), (wGninthN3nXGT19Labs,
        wGninthN3nXGT19Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 5: equal to the odd self part of the group. -/
theorem wGninthN3nX_og5 : (oddSumF 64 false wGninthN3nXHX0 (OctadDense.octChunkTerms
    [(wGninthN3nXGT20Labs, wGninthN3nXGT20Nums, 2048), (wGninthN3nXGT21Labs, wGninthN3nXGT21Nums,
    2048), (wGninthN3nXGT22Labs, wGninthN3nXGT22Nums, 1704)]) : ℚ) / (2 * (((tensorWordDenAll
    wGninthN3nXH : ℚ) * 32) / 2 ^ 4)) =
    wGninthN3nXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN3nXGT20Labs,
        wGninthN3nXGT20Nums, 2048), (wGninthN3nXGT21Labs, wGninthN3nXGT21Nums, 2048),
        (wGninthN3nXGT22Labs, wGninthN3nXGT22Nums, 1704)])) : ℚ) := by
  decide +kernel

/-- The odd short part equals the odd self part of the target (group checks, no predicted values).
-/
theorem wGninthN3nX_ha : (oddWZ 64 false wGninthN3nXHX0 wGninthN3nXW : ℚ) / (2 *
    (((tensorWordDenAll wGninthN3nXH : ℚ) * 32) / 2 ^ 4)) =
    wGninthN3nXW.sden * (selfOddP wGninthN3nXW : ℚ) :=
  oddPart_of_groups 64 false wGninthN3nXHX0 wGninthN3nXW _ wGninthN3nX_WshG wGninthN3nX_sd
      (((tensorWordDenAll wGninthN3nXH : ℚ) * 32) / 2 ^ 4) (by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [wGninthN3nX_og0, wGninthN3nX_og1, wGninthN3nX_og2, wGninthN3nX_og3, wGninthN3nX_og4,
        wGninthN3nX_og5])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
