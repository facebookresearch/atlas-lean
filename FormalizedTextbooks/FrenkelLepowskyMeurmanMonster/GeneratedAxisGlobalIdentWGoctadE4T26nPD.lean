/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE4T26nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE4T26nTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (odd short terms) of the identification Eighth[8]- <-> Tenth[40]+ (record
goctad:E4@T26-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target short block as packed chunks, in groups. -/
theorem wGoctadE4T26n_WshG : wGoctadE4T26nW.sh = ShortData.ofList [OctadDense.octChunkTerms
    [(wGoctadE4T26nGT0Labs, wGoctadE4T26nGT0Nums, 2048), (wGoctadE4T26nGT1Labs,
    wGoctadE4T26nGT1Nums, 2048), (wGoctadE4T26nGT2Labs, wGoctadE4T26nGT2Nums, 2048),
    (wGoctadE4T26nGT3Labs, wGoctadE4T26nGT3Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadE4T26nGT4Labs, wGoctadE4T26nGT4Nums, 2048), (wGoctadE4T26nGT5Labs,
    wGoctadE4T26nGT5Nums, 2048), (wGoctadE4T26nGT6Labs, wGoctadE4T26nGT6Nums, 2048),
    (wGoctadE4T26nGT7Labs, wGoctadE4T26nGT7Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadE4T26nGT8Labs, wGoctadE4T26nGT8Nums, 2048), (wGoctadE4T26nGT9Labs,
    wGoctadE4T26nGT9Nums, 2048), (wGoctadE4T26nGT10Labs, wGoctadE4T26nGT10Nums, 2048),
    (wGoctadE4T26nGT11Labs, wGoctadE4T26nGT11Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadE4T26nGT12Labs, wGoctadE4T26nGT12Nums, 2048), (wGoctadE4T26nGT13Labs,
    wGoctadE4T26nGT13Nums, 2048), (wGoctadE4T26nGT14Labs, wGoctadE4T26nGT14Nums, 2048),
    (wGoctadE4T26nGT15Labs, wGoctadE4T26nGT15Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadE4T26nGT16Labs, wGoctadE4T26nGT16Nums, 2048), (wGoctadE4T26nGT17Labs,
    wGoctadE4T26nGT17Nums, 2048), (wGoctadE4T26nGT18Labs, wGoctadE4T26nGT18Nums, 2048),
    (wGoctadE4T26nGT19Labs, wGoctadE4T26nGT19Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadE4T26nGT20Labs, wGoctadE4T26nGT20Nums, 2048), (wGoctadE4T26nGT21Labs,
    wGoctadE4T26nGT21Nums, 2048), (wGoctadE4T26nGT22Labs, wGoctadE4T26nGT22Nums, 1026)]].flatten
    := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, OctadDense.octChunkTerms,
    List.append_assoc]
  rfl

set_option maxRecDepth 100000 in
/-- The odd labels of the target are distinct. -/
theorem wGoctadE4T26n_sd : labDistinct wGoctadE4T26nW.sh.odd 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 0: equal to the odd self part of the group. -/
theorem wGoctadE4T26n_og0 : (oddSumF 64 false wGoctadE4T26nHX0 (OctadDense.octChunkTerms
    [(wGoctadE4T26nGT0Labs, wGoctadE4T26nGT0Nums, 2048), (wGoctadE4T26nGT1Labs,
    wGoctadE4T26nGT1Nums, 2048), (wGoctadE4T26nGT2Labs, wGoctadE4T26nGT2Nums, 2048),
    (wGoctadE4T26nGT3Labs, wGoctadE4T26nGT3Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGoctadE4T26nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 29)) =
    wGoctadE4T26nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE4T26nGT0Labs,
        wGoctadE4T26nGT0Nums, 2048), (wGoctadE4T26nGT1Labs, wGoctadE4T26nGT1Nums, 2048),
        (wGoctadE4T26nGT2Labs, wGoctadE4T26nGT2Nums, 2048), (wGoctadE4T26nGT3Labs,
        wGoctadE4T26nGT3Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 1: equal to the odd self part of the group. -/
theorem wGoctadE4T26n_og1 : (oddSumF 64 false wGoctadE4T26nHX0 (OctadDense.octChunkTerms
    [(wGoctadE4T26nGT4Labs, wGoctadE4T26nGT4Nums, 2048), (wGoctadE4T26nGT5Labs,
    wGoctadE4T26nGT5Nums, 2048), (wGoctadE4T26nGT6Labs, wGoctadE4T26nGT6Nums, 2048),
    (wGoctadE4T26nGT7Labs, wGoctadE4T26nGT7Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGoctadE4T26nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 29)) =
    wGoctadE4T26nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE4T26nGT4Labs,
        wGoctadE4T26nGT4Nums, 2048), (wGoctadE4T26nGT5Labs, wGoctadE4T26nGT5Nums, 2048),
        (wGoctadE4T26nGT6Labs, wGoctadE4T26nGT6Nums, 2048), (wGoctadE4T26nGT7Labs,
        wGoctadE4T26nGT7Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 2: equal to the odd self part of the group. -/
theorem wGoctadE4T26n_og2 : (oddSumF 64 false wGoctadE4T26nHX0 (OctadDense.octChunkTerms
    [(wGoctadE4T26nGT8Labs, wGoctadE4T26nGT8Nums, 2048), (wGoctadE4T26nGT9Labs,
    wGoctadE4T26nGT9Nums, 2048), (wGoctadE4T26nGT10Labs, wGoctadE4T26nGT10Nums, 2048),
    (wGoctadE4T26nGT11Labs, wGoctadE4T26nGT11Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGoctadE4T26nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 29)) =
    wGoctadE4T26nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE4T26nGT8Labs,
        wGoctadE4T26nGT8Nums, 2048), (wGoctadE4T26nGT9Labs, wGoctadE4T26nGT9Nums, 2048),
        (wGoctadE4T26nGT10Labs, wGoctadE4T26nGT10Nums, 2048), (wGoctadE4T26nGT11Labs,
        wGoctadE4T26nGT11Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 3: equal to the odd self part of the group. -/
theorem wGoctadE4T26n_og3 : (oddSumF 64 false wGoctadE4T26nHX0 (OctadDense.octChunkTerms
    [(wGoctadE4T26nGT12Labs, wGoctadE4T26nGT12Nums, 2048), (wGoctadE4T26nGT13Labs,
    wGoctadE4T26nGT13Nums, 2048), (wGoctadE4T26nGT14Labs, wGoctadE4T26nGT14Nums, 2048),
    (wGoctadE4T26nGT15Labs, wGoctadE4T26nGT15Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGoctadE4T26nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 29)) =
    wGoctadE4T26nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE4T26nGT12Labs,
        wGoctadE4T26nGT12Nums, 2048), (wGoctadE4T26nGT13Labs, wGoctadE4T26nGT13Nums, 2048),
        (wGoctadE4T26nGT14Labs, wGoctadE4T26nGT14Nums, 2048), (wGoctadE4T26nGT15Labs,
        wGoctadE4T26nGT15Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 4: equal to the odd self part of the group. -/
theorem wGoctadE4T26n_og4 : (oddSumF 64 false wGoctadE4T26nHX0 (OctadDense.octChunkTerms
    [(wGoctadE4T26nGT16Labs, wGoctadE4T26nGT16Nums, 2048), (wGoctadE4T26nGT17Labs,
    wGoctadE4T26nGT17Nums, 2048), (wGoctadE4T26nGT18Labs, wGoctadE4T26nGT18Nums, 2048),
    (wGoctadE4T26nGT19Labs, wGoctadE4T26nGT19Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGoctadE4T26nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 29)) =
    wGoctadE4T26nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE4T26nGT16Labs,
        wGoctadE4T26nGT16Nums, 2048), (wGoctadE4T26nGT17Labs, wGoctadE4T26nGT17Nums, 2048),
        (wGoctadE4T26nGT18Labs, wGoctadE4T26nGT18Nums, 2048), (wGoctadE4T26nGT19Labs,
        wGoctadE4T26nGT19Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 5: equal to the odd self part of the group. -/
theorem wGoctadE4T26n_og5 : (oddSumF 64 false wGoctadE4T26nHX0 (OctadDense.octChunkTerms
    [(wGoctadE4T26nGT20Labs, wGoctadE4T26nGT20Nums, 2048), (wGoctadE4T26nGT21Labs,
    wGoctadE4T26nGT21Nums, 2048), (wGoctadE4T26nGT22Labs, wGoctadE4T26nGT22Nums, 1026)]) : ℚ) / (2
    * (((tensorWordDenAll wGoctadE4T26nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2
    ^ 29)) =
    wGoctadE4T26nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE4T26nGT20Labs,
        wGoctadE4T26nGT20Nums, 2048), (wGoctadE4T26nGT21Labs, wGoctadE4T26nGT21Nums, 2048),
        (wGoctadE4T26nGT22Labs, wGoctadE4T26nGT22Nums, 1026)])) : ℚ) := by
  decide +kernel

/-- The odd short part equals the odd self part of the target (group checks, no predicted values).
-/
theorem wGoctadE4T26n_ha : (oddWZ 64 false wGoctadE4T26nHX0 wGoctadE4T26nW : ℚ) / (2 *
    (((tensorWordDenAll wGoctadE4T26nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^
    29)) =
    wGoctadE4T26nW.sden * (selfOddP wGoctadE4T26nW : ℚ) :=
  oddPart_of_groups 64 false wGoctadE4T26nHX0 wGoctadE4T26nW _ wGoctadE4T26n_WshG wGoctadE4T26n_sd
      (((tensorWordDenAll wGoctadE4T26nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2
      ^ 29) (by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [wGoctadE4T26n_og0, wGoctadE4T26n_og1, wGoctadE4T26n_og2, wGoctadE4T26n_og3,
        wGoctadE4T26n_og4, wGoctadE4T26n_og5])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
