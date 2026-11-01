/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN6nXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN6nXTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (odd short terms) of the identification Ninth[10]- <-> Twelfth[12]- (record
gninth:N6-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target short block as packed chunks, in groups. -/
theorem wGninthN6nX_WshG : wGninthN6nXW.sh = ShortData.ofList [OctadDense.octChunkTerms
    [(wGninthN6nXGT0Labs, wGninthN6nXGT0Nums, 2048), (wGninthN6nXGT1Labs, wGninthN6nXGT1Nums,
    2048), (wGninthN6nXGT2Labs, wGninthN6nXGT2Nums, 2048), (wGninthN6nXGT3Labs,
    wGninthN6nXGT3Nums, 2048)], OctadDense.octChunkTerms [(wGninthN6nXGT4Labs, wGninthN6nXGT4Nums,
    2048), (wGninthN6nXGT5Labs, wGninthN6nXGT5Nums, 2048), (wGninthN6nXGT6Labs,
    wGninthN6nXGT6Nums, 2048), (wGninthN6nXGT7Labs, wGninthN6nXGT7Nums, 2048)],
    OctadDense.octChunkTerms [(wGninthN6nXGT8Labs, wGninthN6nXGT8Nums, 2048), (wGninthN6nXGT9Labs,
    wGninthN6nXGT9Nums, 2048), (wGninthN6nXGT10Labs, wGninthN6nXGT10Nums, 2048),
    (wGninthN6nXGT11Labs, wGninthN6nXGT11Nums, 2048)], OctadDense.octChunkTerms
    [(wGninthN6nXGT12Labs, wGninthN6nXGT12Nums, 2048), (wGninthN6nXGT13Labs, wGninthN6nXGT13Nums,
    2048), (wGninthN6nXGT14Labs, wGninthN6nXGT14Nums, 2048), (wGninthN6nXGT15Labs,
    wGninthN6nXGT15Nums, 2048)], OctadDense.octChunkTerms [(wGninthN6nXGT16Labs,
    wGninthN6nXGT16Nums, 2048), (wGninthN6nXGT17Labs, wGninthN6nXGT17Nums, 2048),
    (wGninthN6nXGT18Labs, wGninthN6nXGT18Nums, 2048), (wGninthN6nXGT19Labs, wGninthN6nXGT19Nums,
    2048)], OctadDense.octChunkTerms [(wGninthN6nXGT20Labs, wGninthN6nXGT20Nums, 2048),
    (wGninthN6nXGT21Labs, wGninthN6nXGT21Nums, 2048), (wGninthN6nXGT22Labs, wGninthN6nXGT22Nums,
    1704)]].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, OctadDense.octChunkTerms,
    List.append_assoc]
  rfl

set_option maxRecDepth 100000 in
/-- The odd labels of the target are distinct. -/
theorem wGninthN6nX_sd : labDistinct wGninthN6nXW.sh.odd 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 0: equal to the odd self part of the group. -/
theorem wGninthN6nX_og0 : (oddSumF 64 false wGninthN6nXHX0 (OctadDense.octChunkTerms
    [(wGninthN6nXGT0Labs, wGninthN6nXGT0Nums, 2048), (wGninthN6nXGT1Labs, wGninthN6nXGT1Nums,
    2048), (wGninthN6nXGT2Labs, wGninthN6nXGT2Nums, 2048), (wGninthN6nXGT3Labs,
    wGninthN6nXGT3Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN6nXH : ℚ) * 32) / 2 ^ 16))
    =
    wGninthN6nXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN6nXGT0Labs,
        wGninthN6nXGT0Nums, 2048), (wGninthN6nXGT1Labs, wGninthN6nXGT1Nums, 2048),
        (wGninthN6nXGT2Labs, wGninthN6nXGT2Nums, 2048), (wGninthN6nXGT3Labs, wGninthN6nXGT3Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 1: equal to the odd self part of the group. -/
theorem wGninthN6nX_og1 : (oddSumF 64 false wGninthN6nXHX0 (OctadDense.octChunkTerms
    [(wGninthN6nXGT4Labs, wGninthN6nXGT4Nums, 2048), (wGninthN6nXGT5Labs, wGninthN6nXGT5Nums,
    2048), (wGninthN6nXGT6Labs, wGninthN6nXGT6Nums, 2048), (wGninthN6nXGT7Labs,
    wGninthN6nXGT7Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN6nXH : ℚ) * 32) / 2 ^ 16))
    =
    wGninthN6nXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN6nXGT4Labs,
        wGninthN6nXGT4Nums, 2048), (wGninthN6nXGT5Labs, wGninthN6nXGT5Nums, 2048),
        (wGninthN6nXGT6Labs, wGninthN6nXGT6Nums, 2048), (wGninthN6nXGT7Labs, wGninthN6nXGT7Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 2: equal to the odd self part of the group. -/
theorem wGninthN6nX_og2 : (oddSumF 64 false wGninthN6nXHX0 (OctadDense.octChunkTerms
    [(wGninthN6nXGT8Labs, wGninthN6nXGT8Nums, 2048), (wGninthN6nXGT9Labs, wGninthN6nXGT9Nums,
    2048), (wGninthN6nXGT10Labs, wGninthN6nXGT10Nums, 2048), (wGninthN6nXGT11Labs,
    wGninthN6nXGT11Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN6nXH : ℚ) * 32) / 2 ^
    16)) =
    wGninthN6nXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN6nXGT8Labs,
        wGninthN6nXGT8Nums, 2048), (wGninthN6nXGT9Labs, wGninthN6nXGT9Nums, 2048),
        (wGninthN6nXGT10Labs, wGninthN6nXGT10Nums, 2048), (wGninthN6nXGT11Labs,
        wGninthN6nXGT11Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 3: equal to the odd self part of the group. -/
theorem wGninthN6nX_og3 : (oddSumF 64 false wGninthN6nXHX0 (OctadDense.octChunkTerms
    [(wGninthN6nXGT12Labs, wGninthN6nXGT12Nums, 2048), (wGninthN6nXGT13Labs, wGninthN6nXGT13Nums,
    2048), (wGninthN6nXGT14Labs, wGninthN6nXGT14Nums, 2048), (wGninthN6nXGT15Labs,
    wGninthN6nXGT15Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN6nXH : ℚ) * 32) / 2 ^
    16)) =
    wGninthN6nXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN6nXGT12Labs,
        wGninthN6nXGT12Nums, 2048), (wGninthN6nXGT13Labs, wGninthN6nXGT13Nums, 2048),
        (wGninthN6nXGT14Labs, wGninthN6nXGT14Nums, 2048), (wGninthN6nXGT15Labs,
        wGninthN6nXGT15Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 4: equal to the odd self part of the group. -/
theorem wGninthN6nX_og4 : (oddSumF 64 false wGninthN6nXHX0 (OctadDense.octChunkTerms
    [(wGninthN6nXGT16Labs, wGninthN6nXGT16Nums, 2048), (wGninthN6nXGT17Labs, wGninthN6nXGT17Nums,
    2048), (wGninthN6nXGT18Labs, wGninthN6nXGT18Nums, 2048), (wGninthN6nXGT19Labs,
    wGninthN6nXGT19Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN6nXH : ℚ) * 32) / 2 ^
    16)) =
    wGninthN6nXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN6nXGT16Labs,
        wGninthN6nXGT16Nums, 2048), (wGninthN6nXGT17Labs, wGninthN6nXGT17Nums, 2048),
        (wGninthN6nXGT18Labs, wGninthN6nXGT18Nums, 2048), (wGninthN6nXGT19Labs,
        wGninthN6nXGT19Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 5: equal to the odd self part of the group. -/
theorem wGninthN6nX_og5 : (oddSumF 64 false wGninthN6nXHX0 (OctadDense.octChunkTerms
    [(wGninthN6nXGT20Labs, wGninthN6nXGT20Nums, 2048), (wGninthN6nXGT21Labs, wGninthN6nXGT21Nums,
    2048), (wGninthN6nXGT22Labs, wGninthN6nXGT22Nums, 1704)]) : ℚ) / (2 * (((tensorWordDenAll
    wGninthN6nXH : ℚ) * 32) / 2 ^ 16)) =
    wGninthN6nXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN6nXGT20Labs,
        wGninthN6nXGT20Nums, 2048), (wGninthN6nXGT21Labs, wGninthN6nXGT21Nums, 2048),
        (wGninthN6nXGT22Labs, wGninthN6nXGT22Nums, 1704)])) : ℚ) := by
  decide +kernel

/-- The odd short part equals the odd self part of the target (group checks, no predicted values).
-/
theorem wGninthN6nX_ha : (oddWZ 64 false wGninthN6nXHX0 wGninthN6nXW : ℚ) / (2 *
    (((tensorWordDenAll wGninthN6nXH : ℚ) * 32) / 2 ^ 16)) =
    wGninthN6nXW.sden * (selfOddP wGninthN6nXW : ℚ) :=
  oddPart_of_groups 64 false wGninthN6nXHX0 wGninthN6nXW _ wGninthN6nX_WshG wGninthN6nX_sd
      (((tensorWordDenAll wGninthN6nXH : ℚ) * 32) / 2 ^ 16) (by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [wGninthN6nX_og0, wGninthN6nX_og1, wGninthN6nX_og2, wGninthN6nX_og3, wGninthN6nX_og4,
        wGninthN6nX_og5])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
