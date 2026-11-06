/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGoctadE18nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGoctadE18nTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (odd short terms) of the identification Eighth[23]- <-> Tenth[58]- (record
goctad:E18-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target short block as packed chunks, in groups. -/
theorem wGoctadXGoctadE18n_WshG : wGoctadXGoctadE18nW.sh = ShortData.ofList
    [OctadDense.octChunkTerms [(wGoctadXGoctadE18nGT0Labs, wGoctadXGoctadE18nGT0Nums, 2048),
    (wGoctadXGoctadE18nGT1Labs, wGoctadXGoctadE18nGT1Nums, 2048), (wGoctadXGoctadE18nGT2Labs,
    wGoctadXGoctadE18nGT2Nums, 2048), (wGoctadXGoctadE18nGT3Labs, wGoctadXGoctadE18nGT3Nums,
    2048)], OctadDense.octChunkTerms [(wGoctadXGoctadE18nGT4Labs, wGoctadXGoctadE18nGT4Nums,
    2048), (wGoctadXGoctadE18nGT5Labs, wGoctadXGoctadE18nGT5Nums, 2048),
    (wGoctadXGoctadE18nGT6Labs, wGoctadXGoctadE18nGT6Nums, 2048), (wGoctadXGoctadE18nGT7Labs,
    wGoctadXGoctadE18nGT7Nums, 2048)], OctadDense.octChunkTerms [(wGoctadXGoctadE18nGT8Labs,
    wGoctadXGoctadE18nGT8Nums, 2048), (wGoctadXGoctadE18nGT9Labs, wGoctadXGoctadE18nGT9Nums,
    2048), (wGoctadXGoctadE18nGT10Labs, wGoctadXGoctadE18nGT10Nums, 2048),
    (wGoctadXGoctadE18nGT11Labs, wGoctadXGoctadE18nGT11Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadXGoctadE18nGT12Labs, wGoctadXGoctadE18nGT12Nums, 2048), (wGoctadXGoctadE18nGT13Labs,
    wGoctadXGoctadE18nGT13Nums, 2048), (wGoctadXGoctadE18nGT14Labs, wGoctadXGoctadE18nGT14Nums,
    2048), (wGoctadXGoctadE18nGT15Labs, wGoctadXGoctadE18nGT15Nums, 2048)],
    OctadDense.octChunkTerms [(wGoctadXGoctadE18nGT16Labs, wGoctadXGoctadE18nGT16Nums, 2048),
    (wGoctadXGoctadE18nGT17Labs, wGoctadXGoctadE18nGT17Nums, 2048), (wGoctadXGoctadE18nGT18Labs,
    wGoctadXGoctadE18nGT18Nums, 2048), (wGoctadXGoctadE18nGT19Labs, wGoctadXGoctadE18nGT19Nums,
    2048)], OctadDense.octChunkTerms [(wGoctadXGoctadE18nGT20Labs, wGoctadXGoctadE18nGT20Nums,
    2048), (wGoctadXGoctadE18nGT21Labs, wGoctadXGoctadE18nGT21Nums, 2048),
    (wGoctadXGoctadE18nGT22Labs, wGoctadXGoctadE18nGT22Nums, 1026)]].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, OctadDense.octChunkTerms,
    List.append_assoc]
  rfl

set_option maxRecDepth 100000 in
/-- The odd labels of the target are distinct. -/
theorem wGoctadXGoctadE18n_sd : labDistinct wGoctadXGoctadE18nW.sh.odd 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 0: equal to the odd self part of the group. -/
theorem wGoctadXGoctadE18n_og0 : (oddSumF 64 false wGoctadXGoctadE18nHX0 (OctadDense.octChunkTerms
    [(wGoctadXGoctadE18nGT0Labs, wGoctadXGoctadE18nGT0Nums, 2048), (wGoctadXGoctadE18nGT1Labs,
    wGoctadXGoctadE18nGT1Nums, 2048), (wGoctadXGoctadE18nGT2Labs, wGoctadXGoctadE18nGT2Nums,
    2048), (wGoctadXGoctadE18nGT3Labs, wGoctadXGoctadE18nGT3Nums, 2048)]) : ℚ) / (2 *
    (((tensorWordDenAll wGoctadXGoctadE18nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)))
    / 2 ^ 16)) =
    wGoctadXGoctadE18nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms
        [(wGoctadXGoctadE18nGT0Labs, wGoctadXGoctadE18nGT0Nums, 2048), (wGoctadXGoctadE18nGT1Labs,
        wGoctadXGoctadE18nGT1Nums, 2048), (wGoctadXGoctadE18nGT2Labs, wGoctadXGoctadE18nGT2Nums,
        2048), (wGoctadXGoctadE18nGT3Labs, wGoctadXGoctadE18nGT3Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 1: equal to the odd self part of the group. -/
theorem wGoctadXGoctadE18n_og1 : (oddSumF 64 false wGoctadXGoctadE18nHX0 (OctadDense.octChunkTerms
    [(wGoctadXGoctadE18nGT4Labs, wGoctadXGoctadE18nGT4Nums, 2048), (wGoctadXGoctadE18nGT5Labs,
    wGoctadXGoctadE18nGT5Nums, 2048), (wGoctadXGoctadE18nGT6Labs, wGoctadXGoctadE18nGT6Nums,
    2048), (wGoctadXGoctadE18nGT7Labs, wGoctadXGoctadE18nGT7Nums, 2048)]) : ℚ) / (2 *
    (((tensorWordDenAll wGoctadXGoctadE18nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)))
    / 2 ^ 16)) =
    wGoctadXGoctadE18nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms
        [(wGoctadXGoctadE18nGT4Labs, wGoctadXGoctadE18nGT4Nums, 2048), (wGoctadXGoctadE18nGT5Labs,
        wGoctadXGoctadE18nGT5Nums, 2048), (wGoctadXGoctadE18nGT6Labs, wGoctadXGoctadE18nGT6Nums,
        2048), (wGoctadXGoctadE18nGT7Labs, wGoctadXGoctadE18nGT7Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 2: equal to the odd self part of the group. -/
theorem wGoctadXGoctadE18n_og2 : (oddSumF 64 false wGoctadXGoctadE18nHX0 (OctadDense.octChunkTerms
    [(wGoctadXGoctadE18nGT8Labs, wGoctadXGoctadE18nGT8Nums, 2048), (wGoctadXGoctadE18nGT9Labs,
    wGoctadXGoctadE18nGT9Nums, 2048), (wGoctadXGoctadE18nGT10Labs, wGoctadXGoctadE18nGT10Nums,
    2048), (wGoctadXGoctadE18nGT11Labs, wGoctadXGoctadE18nGT11Nums, 2048)]) : ℚ) / (2 *
    (((tensorWordDenAll wGoctadXGoctadE18nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)))
    / 2 ^ 16)) =
    wGoctadXGoctadE18nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms
        [(wGoctadXGoctadE18nGT8Labs, wGoctadXGoctadE18nGT8Nums, 2048), (wGoctadXGoctadE18nGT9Labs,
        wGoctadXGoctadE18nGT9Nums, 2048), (wGoctadXGoctadE18nGT10Labs, wGoctadXGoctadE18nGT10Nums,
        2048), (wGoctadXGoctadE18nGT11Labs, wGoctadXGoctadE18nGT11Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 3: equal to the odd self part of the group. -/
theorem wGoctadXGoctadE18n_og3 : (oddSumF 64 false wGoctadXGoctadE18nHX0 (OctadDense.octChunkTerms
    [(wGoctadXGoctadE18nGT12Labs, wGoctadXGoctadE18nGT12Nums, 2048), (wGoctadXGoctadE18nGT13Labs,
    wGoctadXGoctadE18nGT13Nums, 2048), (wGoctadXGoctadE18nGT14Labs, wGoctadXGoctadE18nGT14Nums,
    2048), (wGoctadXGoctadE18nGT15Labs, wGoctadXGoctadE18nGT15Nums, 2048)]) : ℚ) / (2 *
    (((tensorWordDenAll wGoctadXGoctadE18nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)))
    / 2 ^ 16)) =
    wGoctadXGoctadE18nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms
        [(wGoctadXGoctadE18nGT12Labs, wGoctadXGoctadE18nGT12Nums, 2048),
        (wGoctadXGoctadE18nGT13Labs, wGoctadXGoctadE18nGT13Nums, 2048),
        (wGoctadXGoctadE18nGT14Labs, wGoctadXGoctadE18nGT14Nums, 2048),
        (wGoctadXGoctadE18nGT15Labs, wGoctadXGoctadE18nGT15Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 4: equal to the odd self part of the group. -/
theorem wGoctadXGoctadE18n_og4 : (oddSumF 64 false wGoctadXGoctadE18nHX0 (OctadDense.octChunkTerms
    [(wGoctadXGoctadE18nGT16Labs, wGoctadXGoctadE18nGT16Nums, 2048), (wGoctadXGoctadE18nGT17Labs,
    wGoctadXGoctadE18nGT17Nums, 2048), (wGoctadXGoctadE18nGT18Labs, wGoctadXGoctadE18nGT18Nums,
    2048), (wGoctadXGoctadE18nGT19Labs, wGoctadXGoctadE18nGT19Nums, 2048)]) : ℚ) / (2 *
    (((tensorWordDenAll wGoctadXGoctadE18nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)))
    / 2 ^ 16)) =
    wGoctadXGoctadE18nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms
        [(wGoctadXGoctadE18nGT16Labs, wGoctadXGoctadE18nGT16Nums, 2048),
        (wGoctadXGoctadE18nGT17Labs, wGoctadXGoctadE18nGT17Nums, 2048),
        (wGoctadXGoctadE18nGT18Labs, wGoctadXGoctadE18nGT18Nums, 2048),
        (wGoctadXGoctadE18nGT19Labs, wGoctadXGoctadE18nGT19Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 5: equal to the odd self part of the group. -/
theorem wGoctadXGoctadE18n_og5 : (oddSumF 64 false wGoctadXGoctadE18nHX0 (OctadDense.octChunkTerms
    [(wGoctadXGoctadE18nGT20Labs, wGoctadXGoctadE18nGT20Nums, 2048), (wGoctadXGoctadE18nGT21Labs,
    wGoctadXGoctadE18nGT21Nums, 2048), (wGoctadXGoctadE18nGT22Labs, wGoctadXGoctadE18nGT22Nums,
    1026)]) : ℚ) / (2 * (((tensorWordDenAll wGoctadXGoctadE18nH : ℚ) * (2 * ((tensorWordDenAll
    srcEighthH : ℚ) * 1))) / 2 ^ 16)) =
    wGoctadXGoctadE18nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms
        [(wGoctadXGoctadE18nGT20Labs, wGoctadXGoctadE18nGT20Nums, 2048),
        (wGoctadXGoctadE18nGT21Labs, wGoctadXGoctadE18nGT21Nums, 2048),
        (wGoctadXGoctadE18nGT22Labs, wGoctadXGoctadE18nGT22Nums, 1026)])) : ℚ) := by
  decide +kernel

/-- The odd short part equals the odd self part of the target (group checks, no predicted values).
-/
theorem wGoctadXGoctadE18n_ha : (oddWZ 64 false wGoctadXGoctadE18nHX0 wGoctadXGoctadE18nW : ℚ) /
    (2 * (((tensorWordDenAll wGoctadXGoctadE18nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) *
    1))) / 2 ^ 16)) =
    wGoctadXGoctadE18nW.sden * (selfOddP wGoctadXGoctadE18nW : ℚ) :=
  oddPart_of_groups 64 false wGoctadXGoctadE18nHX0 wGoctadXGoctadE18nW _ wGoctadXGoctadE18n_WshG
      wGoctadXGoctadE18n_sd (((tensorWordDenAll wGoctadXGoctadE18nH : ℚ) * (2 * ((tensorWordDenAll
      srcEighthH : ℚ) * 1))) / 2 ^ 16) (by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [wGoctadXGoctadE18n_og0, wGoctadXGoctadE18n_og1, wGoctadXGoctadE18n_og2,
        wGoctadXGoctadE18n_og3, wGoctadXGoctadE18n_og4, wGoctadXGoctadE18n_og5])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
