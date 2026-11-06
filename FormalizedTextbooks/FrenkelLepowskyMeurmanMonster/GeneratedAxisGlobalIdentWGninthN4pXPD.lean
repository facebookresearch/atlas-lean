/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN4pXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN4pXTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (odd short terms) of the identification Ninth[6]+ <-> Tenth[74]- (record
gninth:N4+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target short block as packed chunks, in groups. -/
theorem wGninthN4pX_WshG : wGninthN4pXW.sh = ShortData.ofList [OctadDense.octChunkTerms
    [(wGninthN4pXGT0Labs, wGninthN4pXGT0Nums, 2048), (wGninthN4pXGT1Labs, wGninthN4pXGT1Nums,
    2048), (wGninthN4pXGT2Labs, wGninthN4pXGT2Nums, 2048), (wGninthN4pXGT3Labs,
    wGninthN4pXGT3Nums, 2048)], OctadDense.octChunkTerms [(wGninthN4pXGT4Labs, wGninthN4pXGT4Nums,
    2048), (wGninthN4pXGT5Labs, wGninthN4pXGT5Nums, 2048), (wGninthN4pXGT6Labs,
    wGninthN4pXGT6Nums, 2048), (wGninthN4pXGT7Labs, wGninthN4pXGT7Nums, 2048)],
    OctadDense.octChunkTerms [(wGninthN4pXGT8Labs, wGninthN4pXGT8Nums, 2048), (wGninthN4pXGT9Labs,
    wGninthN4pXGT9Nums, 2048), (wGninthN4pXGT10Labs, wGninthN4pXGT10Nums, 2048),
    (wGninthN4pXGT11Labs, wGninthN4pXGT11Nums, 2048)], OctadDense.octChunkTerms
    [(wGninthN4pXGT12Labs, wGninthN4pXGT12Nums, 2048), (wGninthN4pXGT13Labs, wGninthN4pXGT13Nums,
    2048), (wGninthN4pXGT14Labs, wGninthN4pXGT14Nums, 2048), (wGninthN4pXGT15Labs,
    wGninthN4pXGT15Nums, 2048)], OctadDense.octChunkTerms [(wGninthN4pXGT16Labs,
    wGninthN4pXGT16Nums, 2048), (wGninthN4pXGT17Labs, wGninthN4pXGT17Nums, 2048),
    (wGninthN4pXGT18Labs, wGninthN4pXGT18Nums, 2048), (wGninthN4pXGT19Labs, wGninthN4pXGT19Nums,
    2048)], OctadDense.octChunkTerms [(wGninthN4pXGT20Labs, wGninthN4pXGT20Nums, 2048),
    (wGninthN4pXGT21Labs, wGninthN4pXGT21Nums, 2048), (wGninthN4pXGT22Labs, wGninthN4pXGT22Nums,
    1026)]].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, OctadDense.octChunkTerms,
    List.append_assoc]
  rfl

set_option maxRecDepth 100000 in
/-- The odd labels of the target are distinct. -/
theorem wGninthN4pX_sd : labDistinct wGninthN4pXW.sh.odd 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 0: equal to the odd self part of the group. -/
theorem wGninthN4pX_og0 : (oddSumF 64 true wGninthN4pXHX0 (OctadDense.octChunkTerms
    [(wGninthN4pXGT0Labs, wGninthN4pXGT0Nums, 2048), (wGninthN4pXGT1Labs, wGninthN4pXGT1Nums,
    2048), (wGninthN4pXGT2Labs, wGninthN4pXGT2Nums, 2048), (wGninthN4pXGT3Labs,
    wGninthN4pXGT3Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN4pXH : ℚ) * 32) / 2 ^ 4))
    =
    wGninthN4pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN4pXGT0Labs,
        wGninthN4pXGT0Nums, 2048), (wGninthN4pXGT1Labs, wGninthN4pXGT1Nums, 2048),
        (wGninthN4pXGT2Labs, wGninthN4pXGT2Nums, 2048), (wGninthN4pXGT3Labs, wGninthN4pXGT3Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 1: equal to the odd self part of the group. -/
theorem wGninthN4pX_og1 : (oddSumF 64 true wGninthN4pXHX0 (OctadDense.octChunkTerms
    [(wGninthN4pXGT4Labs, wGninthN4pXGT4Nums, 2048), (wGninthN4pXGT5Labs, wGninthN4pXGT5Nums,
    2048), (wGninthN4pXGT6Labs, wGninthN4pXGT6Nums, 2048), (wGninthN4pXGT7Labs,
    wGninthN4pXGT7Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN4pXH : ℚ) * 32) / 2 ^ 4))
    =
    wGninthN4pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN4pXGT4Labs,
        wGninthN4pXGT4Nums, 2048), (wGninthN4pXGT5Labs, wGninthN4pXGT5Nums, 2048),
        (wGninthN4pXGT6Labs, wGninthN4pXGT6Nums, 2048), (wGninthN4pXGT7Labs, wGninthN4pXGT7Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 2: equal to the odd self part of the group. -/
theorem wGninthN4pX_og2 : (oddSumF 64 true wGninthN4pXHX0 (OctadDense.octChunkTerms
    [(wGninthN4pXGT8Labs, wGninthN4pXGT8Nums, 2048), (wGninthN4pXGT9Labs, wGninthN4pXGT9Nums,
    2048), (wGninthN4pXGT10Labs, wGninthN4pXGT10Nums, 2048), (wGninthN4pXGT11Labs,
    wGninthN4pXGT11Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN4pXH : ℚ) * 32) / 2 ^ 4))
    =
    wGninthN4pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN4pXGT8Labs,
        wGninthN4pXGT8Nums, 2048), (wGninthN4pXGT9Labs, wGninthN4pXGT9Nums, 2048),
        (wGninthN4pXGT10Labs, wGninthN4pXGT10Nums, 2048), (wGninthN4pXGT11Labs,
        wGninthN4pXGT11Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 3: equal to the odd self part of the group. -/
theorem wGninthN4pX_og3 : (oddSumF 64 true wGninthN4pXHX0 (OctadDense.octChunkTerms
    [(wGninthN4pXGT12Labs, wGninthN4pXGT12Nums, 2048), (wGninthN4pXGT13Labs, wGninthN4pXGT13Nums,
    2048), (wGninthN4pXGT14Labs, wGninthN4pXGT14Nums, 2048), (wGninthN4pXGT15Labs,
    wGninthN4pXGT15Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN4pXH : ℚ) * 32) / 2 ^ 4))
    =
    wGninthN4pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN4pXGT12Labs,
        wGninthN4pXGT12Nums, 2048), (wGninthN4pXGT13Labs, wGninthN4pXGT13Nums, 2048),
        (wGninthN4pXGT14Labs, wGninthN4pXGT14Nums, 2048), (wGninthN4pXGT15Labs,
        wGninthN4pXGT15Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 4: equal to the odd self part of the group. -/
theorem wGninthN4pX_og4 : (oddSumF 64 true wGninthN4pXHX0 (OctadDense.octChunkTerms
    [(wGninthN4pXGT16Labs, wGninthN4pXGT16Nums, 2048), (wGninthN4pXGT17Labs, wGninthN4pXGT17Nums,
    2048), (wGninthN4pXGT18Labs, wGninthN4pXGT18Nums, 2048), (wGninthN4pXGT19Labs,
    wGninthN4pXGT19Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN4pXH : ℚ) * 32) / 2 ^ 4))
    =
    wGninthN4pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN4pXGT16Labs,
        wGninthN4pXGT16Nums, 2048), (wGninthN4pXGT17Labs, wGninthN4pXGT17Nums, 2048),
        (wGninthN4pXGT18Labs, wGninthN4pXGT18Nums, 2048), (wGninthN4pXGT19Labs,
        wGninthN4pXGT19Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 5: equal to the odd self part of the group. -/
theorem wGninthN4pX_og5 : (oddSumF 64 true wGninthN4pXHX0 (OctadDense.octChunkTerms
    [(wGninthN4pXGT20Labs, wGninthN4pXGT20Nums, 2048), (wGninthN4pXGT21Labs, wGninthN4pXGT21Nums,
    2048), (wGninthN4pXGT22Labs, wGninthN4pXGT22Nums, 1026)]) : ℚ) / (2 * (((tensorWordDenAll
    wGninthN4pXH : ℚ) * 32) / 2 ^ 4)) =
    wGninthN4pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN4pXGT20Labs,
        wGninthN4pXGT20Nums, 2048), (wGninthN4pXGT21Labs, wGninthN4pXGT21Nums, 2048),
        (wGninthN4pXGT22Labs, wGninthN4pXGT22Nums, 1026)])) : ℚ) := by
  decide +kernel

/-- The odd short part equals the odd self part of the target (group checks, no predicted values).
-/
theorem wGninthN4pX_ha : (oddWZ 64 true wGninthN4pXHX0 wGninthN4pXW : ℚ) / (2 *
    (((tensorWordDenAll wGninthN4pXH : ℚ) * 32) / 2 ^ 4)) =
    wGninthN4pXW.sden * (selfOddP wGninthN4pXW : ℚ) :=
  oddPart_of_groups 64 true wGninthN4pXHX0 wGninthN4pXW _ wGninthN4pX_WshG wGninthN4pX_sd
      (((tensorWordDenAll wGninthN4pXH : ℚ) * 32) / 2 ^ 4) (by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [wGninthN4pX_og0, wGninthN4pX_og1, wGninthN4pX_og2, wGninthN4pX_og3, wGninthN4pX_og4,
        wGninthN4pX_og5])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
