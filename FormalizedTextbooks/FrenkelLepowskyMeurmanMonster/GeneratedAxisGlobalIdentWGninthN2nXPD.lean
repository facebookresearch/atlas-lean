/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN2nXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN2nXTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (odd short terms) of the identification Ninth[3]- <-> Tenth[50]+ (record
gninth:N2-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target short block as packed chunks, in groups. -/
theorem wGninthN2nX_WshG : wGninthN2nXW.sh = ShortData.ofList [OctadDense.octChunkTerms
    [(wGninthN2nXGT0Labs, wGninthN2nXGT0Nums, 2048), (wGninthN2nXGT1Labs, wGninthN2nXGT1Nums,
    2048), (wGninthN2nXGT2Labs, wGninthN2nXGT2Nums, 2048), (wGninthN2nXGT3Labs,
    wGninthN2nXGT3Nums, 2048)], OctadDense.octChunkTerms [(wGninthN2nXGT4Labs, wGninthN2nXGT4Nums,
    2048), (wGninthN2nXGT5Labs, wGninthN2nXGT5Nums, 2048), (wGninthN2nXGT6Labs,
    wGninthN2nXGT6Nums, 2048), (wGninthN2nXGT7Labs, wGninthN2nXGT7Nums, 2048)],
    OctadDense.octChunkTerms [(wGninthN2nXGT8Labs, wGninthN2nXGT8Nums, 2048), (wGninthN2nXGT9Labs,
    wGninthN2nXGT9Nums, 2048), (wGninthN2nXGT10Labs, wGninthN2nXGT10Nums, 2048),
    (wGninthN2nXGT11Labs, wGninthN2nXGT11Nums, 2048)], OctadDense.octChunkTerms
    [(wGninthN2nXGT12Labs, wGninthN2nXGT12Nums, 2048), (wGninthN2nXGT13Labs, wGninthN2nXGT13Nums,
    2048), (wGninthN2nXGT14Labs, wGninthN2nXGT14Nums, 2048), (wGninthN2nXGT15Labs,
    wGninthN2nXGT15Nums, 2048)], OctadDense.octChunkTerms [(wGninthN2nXGT16Labs,
    wGninthN2nXGT16Nums, 2048), (wGninthN2nXGT17Labs, wGninthN2nXGT17Nums, 2048),
    (wGninthN2nXGT18Labs, wGninthN2nXGT18Nums, 2048), (wGninthN2nXGT19Labs, wGninthN2nXGT19Nums,
    2048)], OctadDense.octChunkTerms [(wGninthN2nXGT20Labs, wGninthN2nXGT20Nums, 2048),
    (wGninthN2nXGT21Labs, wGninthN2nXGT21Nums, 2048), (wGninthN2nXGT22Labs, wGninthN2nXGT22Nums,
    1026)]].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, OctadDense.octChunkTerms,
    List.append_assoc]
  rfl

set_option maxRecDepth 100000 in
/-- The odd labels of the target are distinct. -/
theorem wGninthN2nX_sd : labDistinct wGninthN2nXW.sh.odd 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 0: equal to the odd self part of the group. -/
theorem wGninthN2nX_og0 : (oddSumF 64 false wGninthN2nXHX0 (OctadDense.octChunkTerms
    [(wGninthN2nXGT0Labs, wGninthN2nXGT0Nums, 2048), (wGninthN2nXGT1Labs, wGninthN2nXGT1Nums,
    2048), (wGninthN2nXGT2Labs, wGninthN2nXGT2Nums, 2048), (wGninthN2nXGT3Labs,
    wGninthN2nXGT3Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN2nXH : ℚ) * 32) / 2 ^ 8))
    =
    wGninthN2nXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN2nXGT0Labs,
        wGninthN2nXGT0Nums, 2048), (wGninthN2nXGT1Labs, wGninthN2nXGT1Nums, 2048),
        (wGninthN2nXGT2Labs, wGninthN2nXGT2Nums, 2048), (wGninthN2nXGT3Labs, wGninthN2nXGT3Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 1: equal to the odd self part of the group. -/
theorem wGninthN2nX_og1 : (oddSumF 64 false wGninthN2nXHX0 (OctadDense.octChunkTerms
    [(wGninthN2nXGT4Labs, wGninthN2nXGT4Nums, 2048), (wGninthN2nXGT5Labs, wGninthN2nXGT5Nums,
    2048), (wGninthN2nXGT6Labs, wGninthN2nXGT6Nums, 2048), (wGninthN2nXGT7Labs,
    wGninthN2nXGT7Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN2nXH : ℚ) * 32) / 2 ^ 8))
    =
    wGninthN2nXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN2nXGT4Labs,
        wGninthN2nXGT4Nums, 2048), (wGninthN2nXGT5Labs, wGninthN2nXGT5Nums, 2048),
        (wGninthN2nXGT6Labs, wGninthN2nXGT6Nums, 2048), (wGninthN2nXGT7Labs, wGninthN2nXGT7Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 2: equal to the odd self part of the group. -/
theorem wGninthN2nX_og2 : (oddSumF 64 false wGninthN2nXHX0 (OctadDense.octChunkTerms
    [(wGninthN2nXGT8Labs, wGninthN2nXGT8Nums, 2048), (wGninthN2nXGT9Labs, wGninthN2nXGT9Nums,
    2048), (wGninthN2nXGT10Labs, wGninthN2nXGT10Nums, 2048), (wGninthN2nXGT11Labs,
    wGninthN2nXGT11Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN2nXH : ℚ) * 32) / 2 ^ 8))
    =
    wGninthN2nXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN2nXGT8Labs,
        wGninthN2nXGT8Nums, 2048), (wGninthN2nXGT9Labs, wGninthN2nXGT9Nums, 2048),
        (wGninthN2nXGT10Labs, wGninthN2nXGT10Nums, 2048), (wGninthN2nXGT11Labs,
        wGninthN2nXGT11Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 3: equal to the odd self part of the group. -/
theorem wGninthN2nX_og3 : (oddSumF 64 false wGninthN2nXHX0 (OctadDense.octChunkTerms
    [(wGninthN2nXGT12Labs, wGninthN2nXGT12Nums, 2048), (wGninthN2nXGT13Labs, wGninthN2nXGT13Nums,
    2048), (wGninthN2nXGT14Labs, wGninthN2nXGT14Nums, 2048), (wGninthN2nXGT15Labs,
    wGninthN2nXGT15Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN2nXH : ℚ) * 32) / 2 ^ 8))
    =
    wGninthN2nXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN2nXGT12Labs,
        wGninthN2nXGT12Nums, 2048), (wGninthN2nXGT13Labs, wGninthN2nXGT13Nums, 2048),
        (wGninthN2nXGT14Labs, wGninthN2nXGT14Nums, 2048), (wGninthN2nXGT15Labs,
        wGninthN2nXGT15Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 4: equal to the odd self part of the group. -/
theorem wGninthN2nX_og4 : (oddSumF 64 false wGninthN2nXHX0 (OctadDense.octChunkTerms
    [(wGninthN2nXGT16Labs, wGninthN2nXGT16Nums, 2048), (wGninthN2nXGT17Labs, wGninthN2nXGT17Nums,
    2048), (wGninthN2nXGT18Labs, wGninthN2nXGT18Nums, 2048), (wGninthN2nXGT19Labs,
    wGninthN2nXGT19Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN2nXH : ℚ) * 32) / 2 ^ 8))
    =
    wGninthN2nXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN2nXGT16Labs,
        wGninthN2nXGT16Nums, 2048), (wGninthN2nXGT17Labs, wGninthN2nXGT17Nums, 2048),
        (wGninthN2nXGT18Labs, wGninthN2nXGT18Nums, 2048), (wGninthN2nXGT19Labs,
        wGninthN2nXGT19Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 5: equal to the odd self part of the group. -/
theorem wGninthN2nX_og5 : (oddSumF 64 false wGninthN2nXHX0 (OctadDense.octChunkTerms
    [(wGninthN2nXGT20Labs, wGninthN2nXGT20Nums, 2048), (wGninthN2nXGT21Labs, wGninthN2nXGT21Nums,
    2048), (wGninthN2nXGT22Labs, wGninthN2nXGT22Nums, 1026)]) : ℚ) / (2 * (((tensorWordDenAll
    wGninthN2nXH : ℚ) * 32) / 2 ^ 8)) =
    wGninthN2nXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN2nXGT20Labs,
        wGninthN2nXGT20Nums, 2048), (wGninthN2nXGT21Labs, wGninthN2nXGT21Nums, 2048),
        (wGninthN2nXGT22Labs, wGninthN2nXGT22Nums, 1026)])) : ℚ) := by
  decide +kernel

/-- The odd short part equals the odd self part of the target (group checks, no predicted values).
-/
theorem wGninthN2nX_ha : (oddWZ 64 false wGninthN2nXHX0 wGninthN2nXW : ℚ) / (2 *
    (((tensorWordDenAll wGninthN2nXH : ℚ) * 32) / 2 ^ 8)) =
    wGninthN2nXW.sden * (selfOddP wGninthN2nXW : ℚ) :=
  oddPart_of_groups 64 false wGninthN2nXHX0 wGninthN2nXW _ wGninthN2nX_WshG wGninthN2nX_sd
      (((tensorWordDenAll wGninthN2nXH : ℚ) * 32) / 2 ^ 8) (by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [wGninthN2nX_og0, wGninthN2nX_og1, wGninthN2nX_og2, wGninthN2nX_og3, wGninthN2nX_og4,
        wGninthN2nX_og5])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
