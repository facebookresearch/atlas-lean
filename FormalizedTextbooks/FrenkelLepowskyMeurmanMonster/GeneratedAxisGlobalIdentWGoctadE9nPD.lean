/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE9nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE9nTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG

/-! # Factory parts (odd short terms) of the identification Eighth[13]- <-> Eighth[13]- (record
goctad:E9-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target short block as packed chunks, in groups. -/
theorem wGoctadE9n_WshG : wGoctadE9nW.sh = ShortData.ofList [OctadDense.octChunkTerms
    [(wGoctadE9nGT0Labs, wGoctadE9nGT0Nums, 2048), (wGoctadE9nGT1Labs, wGoctadE9nGT1Nums, 2048),
    (wGoctadE9nGT2Labs, wGoctadE9nGT2Nums, 2048), (wGoctadE9nGT3Labs, wGoctadE9nGT3Nums, 2048)],
    OctadDense.octChunkTerms [(wGoctadE9nGT4Labs, wGoctadE9nGT4Nums, 2048), (wGoctadE9nGT5Labs,
    wGoctadE9nGT5Nums, 2048), (wGoctadE9nGT6Labs, wGoctadE9nGT6Nums, 2048), (wGoctadE9nGT7Labs,
    wGoctadE9nGT7Nums, 2048)], OctadDense.octChunkTerms [(wGoctadE9nGT8Labs, wGoctadE9nGT8Nums,
    2048), (wGoctadE9nGT9Labs, wGoctadE9nGT9Nums, 2048), (wGoctadE9nGT10Labs, wGoctadE9nGT10Nums,
    2048), (wGoctadE9nGT11Labs, wGoctadE9nGT11Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadE9nGT12Labs, wGoctadE9nGT12Nums, 2048), (wGoctadE9nGT13Labs, wGoctadE9nGT13Nums,
    2048), (wGoctadE9nGT14Labs, wGoctadE9nGT14Nums, 2048), (wGoctadE9nGT15Labs,
    wGoctadE9nGT15Nums, 2048)], OctadDense.octChunkTerms [(wGoctadE9nGT16Labs, wGoctadE9nGT16Nums,
    2048), (wGoctadE9nGT17Labs, wGoctadE9nGT17Nums, 2048), (wGoctadE9nGT18Labs,
    wGoctadE9nGT18Nums, 2048), (wGoctadE9nGT19Labs, wGoctadE9nGT19Nums, 2048)],
    OctadDense.octChunkTerms [(wGoctadE9nGT20Labs, wGoctadE9nGT20Nums, 2048), (wGoctadE9nGT21Labs,
    wGoctadE9nGT21Nums, 668)]].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, OctadDense.octChunkTerms,
    List.append_assoc]
  rfl

set_option maxRecDepth 100000 in
/-- The odd labels of the target are distinct. -/
theorem wGoctadE9n_sd : labDistinct wGoctadE9nW.sh.odd 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 0: equal to the odd self part of the group. -/
theorem wGoctadE9n_og0 : (oddSumF 64 false wGoctadE9nHXn (OctadDense.octChunkTerms
    [(wGoctadE9nGT0Labs, wGoctadE9nGT0Nums, 2048), (wGoctadE9nGT1Labs, wGoctadE9nGT1Nums, 2048),
    (wGoctadE9nGT2Labs, wGoctadE9nGT2Nums, 2048), (wGoctadE9nGT3Labs, wGoctadE9nGT3Nums, 2048)]) :
    ℚ) / (2 * ((tensorWordDenAll wGoctadE9nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) *
    1)))) =
    wGoctadE9nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE9nGT0Labs,
        wGoctadE9nGT0Nums, 2048), (wGoctadE9nGT1Labs, wGoctadE9nGT1Nums, 2048),
        (wGoctadE9nGT2Labs, wGoctadE9nGT2Nums, 2048), (wGoctadE9nGT3Labs, wGoctadE9nGT3Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 1: equal to the odd self part of the group. -/
theorem wGoctadE9n_og1 : (oddSumF 64 false wGoctadE9nHXn (OctadDense.octChunkTerms
    [(wGoctadE9nGT4Labs, wGoctadE9nGT4Nums, 2048), (wGoctadE9nGT5Labs, wGoctadE9nGT5Nums, 2048),
    (wGoctadE9nGT6Labs, wGoctadE9nGT6Nums, 2048), (wGoctadE9nGT7Labs, wGoctadE9nGT7Nums, 2048)]) :
    ℚ) / (2 * ((tensorWordDenAll wGoctadE9nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) *
    1)))) =
    wGoctadE9nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE9nGT4Labs,
        wGoctadE9nGT4Nums, 2048), (wGoctadE9nGT5Labs, wGoctadE9nGT5Nums, 2048),
        (wGoctadE9nGT6Labs, wGoctadE9nGT6Nums, 2048), (wGoctadE9nGT7Labs, wGoctadE9nGT7Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 2: equal to the odd self part of the group. -/
theorem wGoctadE9n_og2 : (oddSumF 64 false wGoctadE9nHXn (OctadDense.octChunkTerms
    [(wGoctadE9nGT8Labs, wGoctadE9nGT8Nums, 2048), (wGoctadE9nGT9Labs, wGoctadE9nGT9Nums, 2048),
    (wGoctadE9nGT10Labs, wGoctadE9nGT10Nums, 2048), (wGoctadE9nGT11Labs, wGoctadE9nGT11Nums,
    2048)]) : ℚ) / (2 * ((tensorWordDenAll wGoctadE9nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH :
    ℚ) * 1)))) =
    wGoctadE9nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE9nGT8Labs,
        wGoctadE9nGT8Nums, 2048), (wGoctadE9nGT9Labs, wGoctadE9nGT9Nums, 2048),
        (wGoctadE9nGT10Labs, wGoctadE9nGT10Nums, 2048), (wGoctadE9nGT11Labs, wGoctadE9nGT11Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 3: equal to the odd self part of the group. -/
theorem wGoctadE9n_og3 : (oddSumF 64 false wGoctadE9nHXn (OctadDense.octChunkTerms
    [(wGoctadE9nGT12Labs, wGoctadE9nGT12Nums, 2048), (wGoctadE9nGT13Labs, wGoctadE9nGT13Nums,
    2048), (wGoctadE9nGT14Labs, wGoctadE9nGT14Nums, 2048), (wGoctadE9nGT15Labs,
    wGoctadE9nGT15Nums, 2048)]) : ℚ) / (2 * ((tensorWordDenAll wGoctadE9nH : ℚ) * (2 *
    ((tensorWordDenAll srcEighthH : ℚ) * 1)))) =
    wGoctadE9nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE9nGT12Labs,
        wGoctadE9nGT12Nums, 2048), (wGoctadE9nGT13Labs, wGoctadE9nGT13Nums, 2048),
        (wGoctadE9nGT14Labs, wGoctadE9nGT14Nums, 2048), (wGoctadE9nGT15Labs, wGoctadE9nGT15Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 4: equal to the odd self part of the group. -/
theorem wGoctadE9n_og4 : (oddSumF 64 false wGoctadE9nHXn (OctadDense.octChunkTerms
    [(wGoctadE9nGT16Labs, wGoctadE9nGT16Nums, 2048), (wGoctadE9nGT17Labs, wGoctadE9nGT17Nums,
    2048), (wGoctadE9nGT18Labs, wGoctadE9nGT18Nums, 2048), (wGoctadE9nGT19Labs,
    wGoctadE9nGT19Nums, 2048)]) : ℚ) / (2 * ((tensorWordDenAll wGoctadE9nH : ℚ) * (2 *
    ((tensorWordDenAll srcEighthH : ℚ) * 1)))) =
    wGoctadE9nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE9nGT16Labs,
        wGoctadE9nGT16Nums, 2048), (wGoctadE9nGT17Labs, wGoctadE9nGT17Nums, 2048),
        (wGoctadE9nGT18Labs, wGoctadE9nGT18Nums, 2048), (wGoctadE9nGT19Labs, wGoctadE9nGT19Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 5: equal to the odd self part of the group. -/
theorem wGoctadE9n_og5 : (oddSumF 64 false wGoctadE9nHXn (OctadDense.octChunkTerms
    [(wGoctadE9nGT20Labs, wGoctadE9nGT20Nums, 2048), (wGoctadE9nGT21Labs, wGoctadE9nGT21Nums,
    668)]) : ℚ) / (2 * ((tensorWordDenAll wGoctadE9nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH :
    ℚ) * 1)))) =
    wGoctadE9nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE9nGT20Labs,
        wGoctadE9nGT20Nums, 2048), (wGoctadE9nGT21Labs, wGoctadE9nGT21Nums, 668)])) : ℚ) := by
  decide +kernel

/-- The odd short part equals the odd self part of the target (group checks, no predicted values).
-/
theorem wGoctadE9n_ha : (oddWZ 64 false wGoctadE9nHXn wGoctadE9nW : ℚ) / (2 * ((tensorWordDenAll
    wGoctadE9nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)))) =
    wGoctadE9nW.sden * (selfOddP wGoctadE9nW : ℚ) :=
  oddPart_of_groups 64 false wGoctadE9nHXn wGoctadE9nW _ wGoctadE9n_WshG wGoctadE9n_sd
      ((tensorWordDenAll wGoctadE9nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) (by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [wGoctadE9n_og0, wGoctadE9n_og1, wGoctadE9n_og2, wGoctadE9n_og3, wGoctadE9n_og4,
        wGoctadE9n_og5])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
