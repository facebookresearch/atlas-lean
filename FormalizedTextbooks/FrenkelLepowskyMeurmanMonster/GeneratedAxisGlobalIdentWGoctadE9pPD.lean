/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE9pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE9pTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG

/-! # Factory parts (odd short terms) of the identification Eighth[13]+ <-> Seventh[14]+ (record
goctad:E9+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target short block as packed chunks, in groups. -/
theorem wGoctadE9p_WshG : wGoctadE9pW.sh = ShortData.ofList [OctadDense.octChunkTerms
    [(wGoctadE9pGT0Labs, wGoctadE9pGT0Nums, 2048), (wGoctadE9pGT1Labs, wGoctadE9pGT1Nums, 2048),
    (wGoctadE9pGT2Labs, wGoctadE9pGT2Nums, 2048), (wGoctadE9pGT3Labs, wGoctadE9pGT3Nums, 2048)],
    OctadDense.octChunkTerms [(wGoctadE9pGT4Labs, wGoctadE9pGT4Nums, 2048), (wGoctadE9pGT5Labs,
    wGoctadE9pGT5Nums, 2048), (wGoctadE9pGT6Labs, wGoctadE9pGT6Nums, 2048), (wGoctadE9pGT7Labs,
    wGoctadE9pGT7Nums, 2048)], OctadDense.octChunkTerms [(wGoctadE9pGT8Labs, wGoctadE9pGT8Nums,
    2048), (wGoctadE9pGT9Labs, wGoctadE9pGT9Nums, 2048), (wGoctadE9pGT10Labs, wGoctadE9pGT10Nums,
    2048), (wGoctadE9pGT11Labs, wGoctadE9pGT11Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadE9pGT12Labs, wGoctadE9pGT12Nums, 2048), (wGoctadE9pGT13Labs, wGoctadE9pGT13Nums,
    1000)]].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, OctadDense.octChunkTerms,
    List.append_assoc]
  rfl

set_option maxRecDepth 100000 in
/-- The odd labels of the target are distinct. -/
theorem wGoctadE9p_sd : labDistinct wGoctadE9pW.sh.odd 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 0: equal to the odd self part of the group. -/
theorem wGoctadE9p_og0 : (oddSumF 64 true wGoctadE9pHXn (OctadDense.octChunkTerms
    [(wGoctadE9pGT0Labs, wGoctadE9pGT0Nums, 2048), (wGoctadE9pGT1Labs, wGoctadE9pGT1Nums, 2048),
    (wGoctadE9pGT2Labs, wGoctadE9pGT2Nums, 2048), (wGoctadE9pGT3Labs, wGoctadE9pGT3Nums, 2048)]) :
    ℚ) / (2 * ((tensorWordDenAll wGoctadE9pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) *
    1)))) =
    wGoctadE9pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE9pGT0Labs,
        wGoctadE9pGT0Nums, 2048), (wGoctadE9pGT1Labs, wGoctadE9pGT1Nums, 2048),
        (wGoctadE9pGT2Labs, wGoctadE9pGT2Nums, 2048), (wGoctadE9pGT3Labs, wGoctadE9pGT3Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 1: equal to the odd self part of the group. -/
theorem wGoctadE9p_og1 : (oddSumF 64 true wGoctadE9pHXn (OctadDense.octChunkTerms
    [(wGoctadE9pGT4Labs, wGoctadE9pGT4Nums, 2048), (wGoctadE9pGT5Labs, wGoctadE9pGT5Nums, 2048),
    (wGoctadE9pGT6Labs, wGoctadE9pGT6Nums, 2048), (wGoctadE9pGT7Labs, wGoctadE9pGT7Nums, 2048)]) :
    ℚ) / (2 * ((tensorWordDenAll wGoctadE9pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) *
    1)))) =
    wGoctadE9pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE9pGT4Labs,
        wGoctadE9pGT4Nums, 2048), (wGoctadE9pGT5Labs, wGoctadE9pGT5Nums, 2048),
        (wGoctadE9pGT6Labs, wGoctadE9pGT6Nums, 2048), (wGoctadE9pGT7Labs, wGoctadE9pGT7Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 2: equal to the odd self part of the group. -/
theorem wGoctadE9p_og2 : (oddSumF 64 true wGoctadE9pHXn (OctadDense.octChunkTerms
    [(wGoctadE9pGT8Labs, wGoctadE9pGT8Nums, 2048), (wGoctadE9pGT9Labs, wGoctadE9pGT9Nums, 2048),
    (wGoctadE9pGT10Labs, wGoctadE9pGT10Nums, 2048), (wGoctadE9pGT11Labs, wGoctadE9pGT11Nums,
    2048)]) : ℚ) / (2 * ((tensorWordDenAll wGoctadE9pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH :
    ℚ) * 1)))) =
    wGoctadE9pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE9pGT8Labs,
        wGoctadE9pGT8Nums, 2048), (wGoctadE9pGT9Labs, wGoctadE9pGT9Nums, 2048),
        (wGoctadE9pGT10Labs, wGoctadE9pGT10Nums, 2048), (wGoctadE9pGT11Labs, wGoctadE9pGT11Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 3: equal to the odd self part of the group. -/
theorem wGoctadE9p_og3 : (oddSumF 64 true wGoctadE9pHXn (OctadDense.octChunkTerms
    [(wGoctadE9pGT12Labs, wGoctadE9pGT12Nums, 2048), (wGoctadE9pGT13Labs, wGoctadE9pGT13Nums,
    1000)]) : ℚ) / (2 * ((tensorWordDenAll wGoctadE9pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH :
    ℚ) * 1)))) =
    wGoctadE9pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE9pGT12Labs,
        wGoctadE9pGT12Nums, 2048), (wGoctadE9pGT13Labs, wGoctadE9pGT13Nums, 1000)])) : ℚ) := by
  decide +kernel

/-- The odd short part equals the odd self part of the target (group checks, no predicted values).
-/
theorem wGoctadE9p_ha : (oddWZ 64 true wGoctadE9pHXn wGoctadE9pW : ℚ) / (2 * ((tensorWordDenAll
    wGoctadE9pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)))) =
    wGoctadE9pW.sden * (selfOddP wGoctadE9pW : ℚ) :=
  oddPart_of_groups 64 true wGoctadE9pHXn wGoctadE9pW _ wGoctadE9p_WshG wGoctadE9p_sd
      ((tensorWordDenAll wGoctadE9pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) (by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl
    exacts [wGoctadE9p_og0, wGoctadE9p_og1, wGoctadE9p_og2, wGoctadE9p_og3])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
