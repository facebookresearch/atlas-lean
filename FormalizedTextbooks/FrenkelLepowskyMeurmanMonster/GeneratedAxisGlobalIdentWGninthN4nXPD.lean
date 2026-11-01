/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN4nXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN4nXTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (odd short terms) of the identification Ninth[6]- <-> Tenth[74]- (record
gninth:N4-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target short block as packed chunks, in groups. -/
theorem wGninthN4nX_WshG : wGninthN4nXW.sh = ShortData.ofList [OctadDense.octChunkTerms
    [(wGninthN4nXGT0Labs, wGninthN4nXGT0Nums, 2048), (wGninthN4nXGT1Labs, wGninthN4nXGT1Nums,
    2048), (wGninthN4nXGT2Labs, wGninthN4nXGT2Nums, 2048), (wGninthN4nXGT3Labs,
    wGninthN4nXGT3Nums, 2048)], OctadDense.octChunkTerms [(wGninthN4nXGT4Labs, wGninthN4nXGT4Nums,
    2048), (wGninthN4nXGT5Labs, wGninthN4nXGT5Nums, 2048), (wGninthN4nXGT6Labs,
    wGninthN4nXGT6Nums, 2048), (wGninthN4nXGT7Labs, wGninthN4nXGT7Nums, 2048)],
    OctadDense.octChunkTerms [(wGninthN4nXGT8Labs, wGninthN4nXGT8Nums, 2048), (wGninthN4nXGT9Labs,
    wGninthN4nXGT9Nums, 2048), (wGninthN4nXGT10Labs, wGninthN4nXGT10Nums, 2048),
    (wGninthN4nXGT11Labs, wGninthN4nXGT11Nums, 2048)], OctadDense.octChunkTerms
    [(wGninthN4nXGT12Labs, wGninthN4nXGT12Nums, 2048), (wGninthN4nXGT13Labs, wGninthN4nXGT13Nums,
    2048), (wGninthN4nXGT14Labs, wGninthN4nXGT14Nums, 2048), (wGninthN4nXGT15Labs,
    wGninthN4nXGT15Nums, 2048)], OctadDense.octChunkTerms [(wGninthN4nXGT16Labs,
    wGninthN4nXGT16Nums, 2048), (wGninthN4nXGT17Labs, wGninthN4nXGT17Nums, 2048),
    (wGninthN4nXGT18Labs, wGninthN4nXGT18Nums, 2048), (wGninthN4nXGT19Labs, wGninthN4nXGT19Nums,
    2048)], OctadDense.octChunkTerms [(wGninthN4nXGT20Labs, wGninthN4nXGT20Nums, 2048),
    (wGninthN4nXGT21Labs, wGninthN4nXGT21Nums, 2048), (wGninthN4nXGT22Labs, wGninthN4nXGT22Nums,
    1026)]].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, OctadDense.octChunkTerms,
    List.append_assoc]
  rfl

set_option maxRecDepth 100000 in
/-- The odd labels of the target are distinct. -/
theorem wGninthN4nX_sd : labDistinct wGninthN4nXW.sh.odd 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 0: equal to the odd self part of the group. -/
theorem wGninthN4nX_og0 : (oddSumF 64 false wGninthN4nXHX0 (OctadDense.octChunkTerms
    [(wGninthN4nXGT0Labs, wGninthN4nXGT0Nums, 2048), (wGninthN4nXGT1Labs, wGninthN4nXGT1Nums,
    2048), (wGninthN4nXGT2Labs, wGninthN4nXGT2Nums, 2048), (wGninthN4nXGT3Labs,
    wGninthN4nXGT3Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN4nXH : ℚ) * 32) / 2 ^ 4))
    =
    wGninthN4nXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN4nXGT0Labs,
        wGninthN4nXGT0Nums, 2048), (wGninthN4nXGT1Labs, wGninthN4nXGT1Nums, 2048),
        (wGninthN4nXGT2Labs, wGninthN4nXGT2Nums, 2048), (wGninthN4nXGT3Labs, wGninthN4nXGT3Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 1: equal to the odd self part of the group. -/
theorem wGninthN4nX_og1 : (oddSumF 64 false wGninthN4nXHX0 (OctadDense.octChunkTerms
    [(wGninthN4nXGT4Labs, wGninthN4nXGT4Nums, 2048), (wGninthN4nXGT5Labs, wGninthN4nXGT5Nums,
    2048), (wGninthN4nXGT6Labs, wGninthN4nXGT6Nums, 2048), (wGninthN4nXGT7Labs,
    wGninthN4nXGT7Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN4nXH : ℚ) * 32) / 2 ^ 4))
    =
    wGninthN4nXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN4nXGT4Labs,
        wGninthN4nXGT4Nums, 2048), (wGninthN4nXGT5Labs, wGninthN4nXGT5Nums, 2048),
        (wGninthN4nXGT6Labs, wGninthN4nXGT6Nums, 2048), (wGninthN4nXGT7Labs, wGninthN4nXGT7Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 2: equal to the odd self part of the group. -/
theorem wGninthN4nX_og2 : (oddSumF 64 false wGninthN4nXHX0 (OctadDense.octChunkTerms
    [(wGninthN4nXGT8Labs, wGninthN4nXGT8Nums, 2048), (wGninthN4nXGT9Labs, wGninthN4nXGT9Nums,
    2048), (wGninthN4nXGT10Labs, wGninthN4nXGT10Nums, 2048), (wGninthN4nXGT11Labs,
    wGninthN4nXGT11Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN4nXH : ℚ) * 32) / 2 ^ 4))
    =
    wGninthN4nXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN4nXGT8Labs,
        wGninthN4nXGT8Nums, 2048), (wGninthN4nXGT9Labs, wGninthN4nXGT9Nums, 2048),
        (wGninthN4nXGT10Labs, wGninthN4nXGT10Nums, 2048), (wGninthN4nXGT11Labs,
        wGninthN4nXGT11Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 3: equal to the odd self part of the group. -/
theorem wGninthN4nX_og3 : (oddSumF 64 false wGninthN4nXHX0 (OctadDense.octChunkTerms
    [(wGninthN4nXGT12Labs, wGninthN4nXGT12Nums, 2048), (wGninthN4nXGT13Labs, wGninthN4nXGT13Nums,
    2048), (wGninthN4nXGT14Labs, wGninthN4nXGT14Nums, 2048), (wGninthN4nXGT15Labs,
    wGninthN4nXGT15Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN4nXH : ℚ) * 32) / 2 ^ 4))
    =
    wGninthN4nXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN4nXGT12Labs,
        wGninthN4nXGT12Nums, 2048), (wGninthN4nXGT13Labs, wGninthN4nXGT13Nums, 2048),
        (wGninthN4nXGT14Labs, wGninthN4nXGT14Nums, 2048), (wGninthN4nXGT15Labs,
        wGninthN4nXGT15Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 4: equal to the odd self part of the group. -/
theorem wGninthN4nX_og4 : (oddSumF 64 false wGninthN4nXHX0 (OctadDense.octChunkTerms
    [(wGninthN4nXGT16Labs, wGninthN4nXGT16Nums, 2048), (wGninthN4nXGT17Labs, wGninthN4nXGT17Nums,
    2048), (wGninthN4nXGT18Labs, wGninthN4nXGT18Nums, 2048), (wGninthN4nXGT19Labs,
    wGninthN4nXGT19Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN4nXH : ℚ) * 32) / 2 ^ 4))
    =
    wGninthN4nXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN4nXGT16Labs,
        wGninthN4nXGT16Nums, 2048), (wGninthN4nXGT17Labs, wGninthN4nXGT17Nums, 2048),
        (wGninthN4nXGT18Labs, wGninthN4nXGT18Nums, 2048), (wGninthN4nXGT19Labs,
        wGninthN4nXGT19Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 5: equal to the odd self part of the group. -/
theorem wGninthN4nX_og5 : (oddSumF 64 false wGninthN4nXHX0 (OctadDense.octChunkTerms
    [(wGninthN4nXGT20Labs, wGninthN4nXGT20Nums, 2048), (wGninthN4nXGT21Labs, wGninthN4nXGT21Nums,
    2048), (wGninthN4nXGT22Labs, wGninthN4nXGT22Nums, 1026)]) : ℚ) / (2 * (((tensorWordDenAll
    wGninthN4nXH : ℚ) * 32) / 2 ^ 4)) =
    wGninthN4nXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN4nXGT20Labs,
        wGninthN4nXGT20Nums, 2048), (wGninthN4nXGT21Labs, wGninthN4nXGT21Nums, 2048),
        (wGninthN4nXGT22Labs, wGninthN4nXGT22Nums, 1026)])) : ℚ) := by
  decide +kernel

/-- The odd short part equals the odd self part of the target (group checks, no predicted values).
-/
theorem wGninthN4nX_ha : (oddWZ 64 false wGninthN4nXHX0 wGninthN4nXW : ℚ) / (2 *
    (((tensorWordDenAll wGninthN4nXH : ℚ) * 32) / 2 ^ 4)) =
    wGninthN4nXW.sden * (selfOddP wGninthN4nXW : ℚ) :=
  oddPart_of_groups 64 false wGninthN4nXHX0 wGninthN4nXW _ wGninthN4nX_WshG wGninthN4nX_sd
      (((tensorWordDenAll wGninthN4nXH : ℚ) * 32) / 2 ^ 4) (by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [wGninthN4nX_og0, wGninthN4nX_og1, wGninthN4nX_og2, wGninthN4nX_og3, wGninthN4nX_og4,
        wGninthN4nX_og5])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
