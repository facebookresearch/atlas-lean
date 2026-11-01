/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN2pXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN2pXTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (odd short terms) of the identification Ninth[3]+ <-> Tenth[50]+ (record
gninth:N2+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target short block as packed chunks, in groups. -/
theorem wGninthN2pX_WshG : wGninthN2pXW.sh = ShortData.ofList [OctadDense.octChunkTerms
    [(wGninthN2pXGT0Labs, wGninthN2pXGT0Nums, 2048), (wGninthN2pXGT1Labs, wGninthN2pXGT1Nums,
    2048), (wGninthN2pXGT2Labs, wGninthN2pXGT2Nums, 2048), (wGninthN2pXGT3Labs,
    wGninthN2pXGT3Nums, 2048)], OctadDense.octChunkTerms [(wGninthN2pXGT4Labs, wGninthN2pXGT4Nums,
    2048), (wGninthN2pXGT5Labs, wGninthN2pXGT5Nums, 2048), (wGninthN2pXGT6Labs,
    wGninthN2pXGT6Nums, 2048), (wGninthN2pXGT7Labs, wGninthN2pXGT7Nums, 2048)],
    OctadDense.octChunkTerms [(wGninthN2pXGT8Labs, wGninthN2pXGT8Nums, 2048), (wGninthN2pXGT9Labs,
    wGninthN2pXGT9Nums, 2048), (wGninthN2pXGT10Labs, wGninthN2pXGT10Nums, 2048),
    (wGninthN2pXGT11Labs, wGninthN2pXGT11Nums, 2048)], OctadDense.octChunkTerms
    [(wGninthN2pXGT12Labs, wGninthN2pXGT12Nums, 2048), (wGninthN2pXGT13Labs, wGninthN2pXGT13Nums,
    2048), (wGninthN2pXGT14Labs, wGninthN2pXGT14Nums, 2048), (wGninthN2pXGT15Labs,
    wGninthN2pXGT15Nums, 2048)], OctadDense.octChunkTerms [(wGninthN2pXGT16Labs,
    wGninthN2pXGT16Nums, 2048), (wGninthN2pXGT17Labs, wGninthN2pXGT17Nums, 2048),
    (wGninthN2pXGT18Labs, wGninthN2pXGT18Nums, 2048), (wGninthN2pXGT19Labs, wGninthN2pXGT19Nums,
    2048)], OctadDense.octChunkTerms [(wGninthN2pXGT20Labs, wGninthN2pXGT20Nums, 2048),
    (wGninthN2pXGT21Labs, wGninthN2pXGT21Nums, 2048), (wGninthN2pXGT22Labs, wGninthN2pXGT22Nums,
    1026)]].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, OctadDense.octChunkTerms,
    List.append_assoc]
  rfl

set_option maxRecDepth 100000 in
/-- The odd labels of the target are distinct. -/
theorem wGninthN2pX_sd : labDistinct wGninthN2pXW.sh.odd 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 0: equal to the odd self part of the group. -/
theorem wGninthN2pX_og0 : (oddSumF 64 true wGninthN2pXHX0 (OctadDense.octChunkTerms
    [(wGninthN2pXGT0Labs, wGninthN2pXGT0Nums, 2048), (wGninthN2pXGT1Labs, wGninthN2pXGT1Nums,
    2048), (wGninthN2pXGT2Labs, wGninthN2pXGT2Nums, 2048), (wGninthN2pXGT3Labs,
    wGninthN2pXGT3Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN2pXH : ℚ) * 32) / 2 ^ 8))
    =
    wGninthN2pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN2pXGT0Labs,
        wGninthN2pXGT0Nums, 2048), (wGninthN2pXGT1Labs, wGninthN2pXGT1Nums, 2048),
        (wGninthN2pXGT2Labs, wGninthN2pXGT2Nums, 2048), (wGninthN2pXGT3Labs, wGninthN2pXGT3Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 1: equal to the odd self part of the group. -/
theorem wGninthN2pX_og1 : (oddSumF 64 true wGninthN2pXHX0 (OctadDense.octChunkTerms
    [(wGninthN2pXGT4Labs, wGninthN2pXGT4Nums, 2048), (wGninthN2pXGT5Labs, wGninthN2pXGT5Nums,
    2048), (wGninthN2pXGT6Labs, wGninthN2pXGT6Nums, 2048), (wGninthN2pXGT7Labs,
    wGninthN2pXGT7Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN2pXH : ℚ) * 32) / 2 ^ 8))
    =
    wGninthN2pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN2pXGT4Labs,
        wGninthN2pXGT4Nums, 2048), (wGninthN2pXGT5Labs, wGninthN2pXGT5Nums, 2048),
        (wGninthN2pXGT6Labs, wGninthN2pXGT6Nums, 2048), (wGninthN2pXGT7Labs, wGninthN2pXGT7Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 2: equal to the odd self part of the group. -/
theorem wGninthN2pX_og2 : (oddSumF 64 true wGninthN2pXHX0 (OctadDense.octChunkTerms
    [(wGninthN2pXGT8Labs, wGninthN2pXGT8Nums, 2048), (wGninthN2pXGT9Labs, wGninthN2pXGT9Nums,
    2048), (wGninthN2pXGT10Labs, wGninthN2pXGT10Nums, 2048), (wGninthN2pXGT11Labs,
    wGninthN2pXGT11Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN2pXH : ℚ) * 32) / 2 ^ 8))
    =
    wGninthN2pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN2pXGT8Labs,
        wGninthN2pXGT8Nums, 2048), (wGninthN2pXGT9Labs, wGninthN2pXGT9Nums, 2048),
        (wGninthN2pXGT10Labs, wGninthN2pXGT10Nums, 2048), (wGninthN2pXGT11Labs,
        wGninthN2pXGT11Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 3: equal to the odd self part of the group. -/
theorem wGninthN2pX_og3 : (oddSumF 64 true wGninthN2pXHX0 (OctadDense.octChunkTerms
    [(wGninthN2pXGT12Labs, wGninthN2pXGT12Nums, 2048), (wGninthN2pXGT13Labs, wGninthN2pXGT13Nums,
    2048), (wGninthN2pXGT14Labs, wGninthN2pXGT14Nums, 2048), (wGninthN2pXGT15Labs,
    wGninthN2pXGT15Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN2pXH : ℚ) * 32) / 2 ^ 8))
    =
    wGninthN2pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN2pXGT12Labs,
        wGninthN2pXGT12Nums, 2048), (wGninthN2pXGT13Labs, wGninthN2pXGT13Nums, 2048),
        (wGninthN2pXGT14Labs, wGninthN2pXGT14Nums, 2048), (wGninthN2pXGT15Labs,
        wGninthN2pXGT15Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 4: equal to the odd self part of the group. -/
theorem wGninthN2pX_og4 : (oddSumF 64 true wGninthN2pXHX0 (OctadDense.octChunkTerms
    [(wGninthN2pXGT16Labs, wGninthN2pXGT16Nums, 2048), (wGninthN2pXGT17Labs, wGninthN2pXGT17Nums,
    2048), (wGninthN2pXGT18Labs, wGninthN2pXGT18Nums, 2048), (wGninthN2pXGT19Labs,
    wGninthN2pXGT19Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wGninthN2pXH : ℚ) * 32) / 2 ^ 8))
    =
    wGninthN2pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN2pXGT16Labs,
        wGninthN2pXGT16Nums, 2048), (wGninthN2pXGT17Labs, wGninthN2pXGT17Nums, 2048),
        (wGninthN2pXGT18Labs, wGninthN2pXGT18Nums, 2048), (wGninthN2pXGT19Labs,
        wGninthN2pXGT19Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 5: equal to the odd self part of the group. -/
theorem wGninthN2pX_og5 : (oddSumF 64 true wGninthN2pXHX0 (OctadDense.octChunkTerms
    [(wGninthN2pXGT20Labs, wGninthN2pXGT20Nums, 2048), (wGninthN2pXGT21Labs, wGninthN2pXGT21Nums,
    2048), (wGninthN2pXGT22Labs, wGninthN2pXGT22Nums, 1026)]) : ℚ) / (2 * (((tensorWordDenAll
    wGninthN2pXH : ℚ) * 32) / 2 ^ 8)) =
    wGninthN2pXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN2pXGT20Labs,
        wGninthN2pXGT20Nums, 2048), (wGninthN2pXGT21Labs, wGninthN2pXGT21Nums, 2048),
        (wGninthN2pXGT22Labs, wGninthN2pXGT22Nums, 1026)])) : ℚ) := by
  decide +kernel

/-- The odd short part equals the odd self part of the target (group checks, no predicted values).
-/
theorem wGninthN2pX_ha : (oddWZ 64 true wGninthN2pXHX0 wGninthN2pXW : ℚ) / (2 *
    (((tensorWordDenAll wGninthN2pXH : ℚ) * 32) / 2 ^ 8)) =
    wGninthN2pXW.sden * (selfOddP wGninthN2pXW : ℚ) :=
  oddPart_of_groups 64 true wGninthN2pXHX0 wGninthN2pXW _ wGninthN2pX_WshG wGninthN2pX_sd
      (((tensorWordDenAll wGninthN2pXH : ℚ) * 32) / 2 ^ 8) (by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [wGninthN2pX_og0, wGninthN2pX_og1, wGninthN2pX_og2, wGninthN2pX_og3, wGninthN2pX_og4,
        wGninthN2pX_og5])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
