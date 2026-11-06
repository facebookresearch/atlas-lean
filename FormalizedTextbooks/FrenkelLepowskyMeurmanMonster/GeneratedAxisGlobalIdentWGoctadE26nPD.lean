/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE26nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE26nTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (odd short terms) of the identification Eighth[37]- <-> Seventh[1]+ (record
goctad:E26-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target short block as packed chunks, in groups. -/
theorem wGoctadE26n_WshG : wGoctadE26nW.sh = ShortData.ofList [OctadDense.octChunkTerms
    [(wGoctadE26nGT0Labs, wGoctadE26nGT0Nums, 2048), (wGoctadE26nGT1Labs, wGoctadE26nGT1Nums,
    2048), (wGoctadE26nGT2Labs, wGoctadE26nGT2Nums, 2048), (wGoctadE26nGT3Labs,
    wGoctadE26nGT3Nums, 2048)], OctadDense.octChunkTerms [(wGoctadE26nGT4Labs, wGoctadE26nGT4Nums,
    2048), (wGoctadE26nGT5Labs, wGoctadE26nGT5Nums, 2048), (wGoctadE26nGT6Labs,
    wGoctadE26nGT6Nums, 2048), (wGoctadE26nGT7Labs, wGoctadE26nGT7Nums, 2048)],
    OctadDense.octChunkTerms [(wGoctadE26nGT8Labs, wGoctadE26nGT8Nums, 2048), (wGoctadE26nGT9Labs,
    wGoctadE26nGT9Nums, 2048), (wGoctadE26nGT10Labs, wGoctadE26nGT10Nums, 2048),
    (wGoctadE26nGT11Labs, wGoctadE26nGT11Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadE26nGT12Labs, wGoctadE26nGT12Nums, 2048), (wGoctadE26nGT13Labs, wGoctadE26nGT13Nums,
    1000)]].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, OctadDense.octChunkTerms,
    List.append_assoc]
  rfl

set_option maxRecDepth 100000 in
/-- The odd labels of the target are distinct. -/
theorem wGoctadE26n_sd : labDistinct wGoctadE26nW.sh.odd 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 0: equal to the odd self part of the group. -/
theorem wGoctadE26n_og0 : (oddSumF 64 false wGoctadE26nHXn (OctadDense.octChunkTerms
    [(wGoctadE26nGT0Labs, wGoctadE26nGT0Nums, 2048), (wGoctadE26nGT1Labs, wGoctadE26nGT1Nums,
    2048), (wGoctadE26nGT2Labs, wGoctadE26nGT2Nums, 2048), (wGoctadE26nGT3Labs,
    wGoctadE26nGT3Nums, 2048)]) : ℚ) / (2 * ((tensorWordDenAll wGoctadE26nH : ℚ) * (2 *
    ((tensorWordDenAll srcEighthH : ℚ) * 1)))) =
    wGoctadE26nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE26nGT0Labs,
        wGoctadE26nGT0Nums, 2048), (wGoctadE26nGT1Labs, wGoctadE26nGT1Nums, 2048),
        (wGoctadE26nGT2Labs, wGoctadE26nGT2Nums, 2048), (wGoctadE26nGT3Labs, wGoctadE26nGT3Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 1: equal to the odd self part of the group. -/
theorem wGoctadE26n_og1 : (oddSumF 64 false wGoctadE26nHXn (OctadDense.octChunkTerms
    [(wGoctadE26nGT4Labs, wGoctadE26nGT4Nums, 2048), (wGoctadE26nGT5Labs, wGoctadE26nGT5Nums,
    2048), (wGoctadE26nGT6Labs, wGoctadE26nGT6Nums, 2048), (wGoctadE26nGT7Labs,
    wGoctadE26nGT7Nums, 2048)]) : ℚ) / (2 * ((tensorWordDenAll wGoctadE26nH : ℚ) * (2 *
    ((tensorWordDenAll srcEighthH : ℚ) * 1)))) =
    wGoctadE26nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE26nGT4Labs,
        wGoctadE26nGT4Nums, 2048), (wGoctadE26nGT5Labs, wGoctadE26nGT5Nums, 2048),
        (wGoctadE26nGT6Labs, wGoctadE26nGT6Nums, 2048), (wGoctadE26nGT7Labs, wGoctadE26nGT7Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 2: equal to the odd self part of the group. -/
theorem wGoctadE26n_og2 : (oddSumF 64 false wGoctadE26nHXn (OctadDense.octChunkTerms
    [(wGoctadE26nGT8Labs, wGoctadE26nGT8Nums, 2048), (wGoctadE26nGT9Labs, wGoctadE26nGT9Nums,
    2048), (wGoctadE26nGT10Labs, wGoctadE26nGT10Nums, 2048), (wGoctadE26nGT11Labs,
    wGoctadE26nGT11Nums, 2048)]) : ℚ) / (2 * ((tensorWordDenAll wGoctadE26nH : ℚ) * (2 *
    ((tensorWordDenAll srcEighthH : ℚ) * 1)))) =
    wGoctadE26nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE26nGT8Labs,
        wGoctadE26nGT8Nums, 2048), (wGoctadE26nGT9Labs, wGoctadE26nGT9Nums, 2048),
        (wGoctadE26nGT10Labs, wGoctadE26nGT10Nums, 2048), (wGoctadE26nGT11Labs,
        wGoctadE26nGT11Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 3: equal to the odd self part of the group. -/
theorem wGoctadE26n_og3 : (oddSumF 64 false wGoctadE26nHXn (OctadDense.octChunkTerms
    [(wGoctadE26nGT12Labs, wGoctadE26nGT12Nums, 2048), (wGoctadE26nGT13Labs, wGoctadE26nGT13Nums,
    1000)]) : ℚ) / (2 * ((tensorWordDenAll wGoctadE26nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH
    : ℚ) * 1)))) =
    wGoctadE26nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE26nGT12Labs,
        wGoctadE26nGT12Nums, 2048), (wGoctadE26nGT13Labs, wGoctadE26nGT13Nums, 1000)])) : ℚ) := by
  decide +kernel

/-- The odd short part equals the odd self part of the target (group checks, no predicted values).
-/
theorem wGoctadE26n_ha : (oddWZ 64 false wGoctadE26nHXn wGoctadE26nW : ℚ) / (2 *
    ((tensorWordDenAll wGoctadE26nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)))) =
    wGoctadE26nW.sden * (selfOddP wGoctadE26nW : ℚ) :=
  oddPart_of_groups 64 false wGoctadE26nHXn wGoctadE26nW _ wGoctadE26n_WshG wGoctadE26n_sd
      ((tensorWordDenAll wGoctadE26nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) (by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl
    exacts [wGoctadE26n_og0, wGoctadE26n_og1, wGoctadE26n_og2, wGoctadE26n_og3])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
