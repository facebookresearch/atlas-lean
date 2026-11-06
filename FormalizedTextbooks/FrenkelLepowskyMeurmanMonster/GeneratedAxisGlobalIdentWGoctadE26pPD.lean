/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE26pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE26pTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (odd short terms) of the identification Eighth[37]+ <-> Seventh[32]+ (record
goctad:E26+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target short block as packed chunks, in groups. -/
theorem wGoctadE26p_WshG : wGoctadE26pW.sh = ShortData.ofList [OctadDense.octChunkTerms
    [(wGoctadE26pGT0Labs, wGoctadE26pGT0Nums, 2048), (wGoctadE26pGT1Labs, wGoctadE26pGT1Nums,
    2048), (wGoctadE26pGT2Labs, wGoctadE26pGT2Nums, 2048), (wGoctadE26pGT3Labs,
    wGoctadE26pGT3Nums, 2048)], OctadDense.octChunkTerms [(wGoctadE26pGT4Labs, wGoctadE26pGT4Nums,
    2048), (wGoctadE26pGT5Labs, wGoctadE26pGT5Nums, 2048), (wGoctadE26pGT6Labs,
    wGoctadE26pGT6Nums, 2048), (wGoctadE26pGT7Labs, wGoctadE26pGT7Nums, 2048)],
    OctadDense.octChunkTerms [(wGoctadE26pGT8Labs, wGoctadE26pGT8Nums, 2048), (wGoctadE26pGT9Labs,
    wGoctadE26pGT9Nums, 2048), (wGoctadE26pGT10Labs, wGoctadE26pGT10Nums, 2048),
    (wGoctadE26pGT11Labs, wGoctadE26pGT11Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadE26pGT12Labs, wGoctadE26pGT12Nums, 2048), (wGoctadE26pGT13Labs, wGoctadE26pGT13Nums,
    1000)]].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, OctadDense.octChunkTerms,
    List.append_assoc]
  rfl

set_option maxRecDepth 100000 in
/-- The odd labels of the target are distinct. -/
theorem wGoctadE26p_sd : labDistinct wGoctadE26pW.sh.odd 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 0: equal to the odd self part of the group. -/
theorem wGoctadE26p_og0 : (oddSumF 64 true wGoctadE26pHXn (OctadDense.octChunkTerms
    [(wGoctadE26pGT0Labs, wGoctadE26pGT0Nums, 2048), (wGoctadE26pGT1Labs, wGoctadE26pGT1Nums,
    2048), (wGoctadE26pGT2Labs, wGoctadE26pGT2Nums, 2048), (wGoctadE26pGT3Labs,
    wGoctadE26pGT3Nums, 2048)]) : ℚ) / (2 * ((tensorWordDenAll wGoctadE26pH : ℚ) * (2 *
    ((tensorWordDenAll srcEighthH : ℚ) * 1)))) =
    wGoctadE26pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE26pGT0Labs,
        wGoctadE26pGT0Nums, 2048), (wGoctadE26pGT1Labs, wGoctadE26pGT1Nums, 2048),
        (wGoctadE26pGT2Labs, wGoctadE26pGT2Nums, 2048), (wGoctadE26pGT3Labs, wGoctadE26pGT3Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 1: equal to the odd self part of the group. -/
theorem wGoctadE26p_og1 : (oddSumF 64 true wGoctadE26pHXn (OctadDense.octChunkTerms
    [(wGoctadE26pGT4Labs, wGoctadE26pGT4Nums, 2048), (wGoctadE26pGT5Labs, wGoctadE26pGT5Nums,
    2048), (wGoctadE26pGT6Labs, wGoctadE26pGT6Nums, 2048), (wGoctadE26pGT7Labs,
    wGoctadE26pGT7Nums, 2048)]) : ℚ) / (2 * ((tensorWordDenAll wGoctadE26pH : ℚ) * (2 *
    ((tensorWordDenAll srcEighthH : ℚ) * 1)))) =
    wGoctadE26pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE26pGT4Labs,
        wGoctadE26pGT4Nums, 2048), (wGoctadE26pGT5Labs, wGoctadE26pGT5Nums, 2048),
        (wGoctadE26pGT6Labs, wGoctadE26pGT6Nums, 2048), (wGoctadE26pGT7Labs, wGoctadE26pGT7Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 2: equal to the odd self part of the group. -/
theorem wGoctadE26p_og2 : (oddSumF 64 true wGoctadE26pHXn (OctadDense.octChunkTerms
    [(wGoctadE26pGT8Labs, wGoctadE26pGT8Nums, 2048), (wGoctadE26pGT9Labs, wGoctadE26pGT9Nums,
    2048), (wGoctadE26pGT10Labs, wGoctadE26pGT10Nums, 2048), (wGoctadE26pGT11Labs,
    wGoctadE26pGT11Nums, 2048)]) : ℚ) / (2 * ((tensorWordDenAll wGoctadE26pH : ℚ) * (2 *
    ((tensorWordDenAll srcEighthH : ℚ) * 1)))) =
    wGoctadE26pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE26pGT8Labs,
        wGoctadE26pGT8Nums, 2048), (wGoctadE26pGT9Labs, wGoctadE26pGT9Nums, 2048),
        (wGoctadE26pGT10Labs, wGoctadE26pGT10Nums, 2048), (wGoctadE26pGT11Labs,
        wGoctadE26pGT11Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 3: equal to the odd self part of the group. -/
theorem wGoctadE26p_og3 : (oddSumF 64 true wGoctadE26pHXn (OctadDense.octChunkTerms
    [(wGoctadE26pGT12Labs, wGoctadE26pGT12Nums, 2048), (wGoctadE26pGT13Labs, wGoctadE26pGT13Nums,
    1000)]) : ℚ) / (2 * ((tensorWordDenAll wGoctadE26pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH
    : ℚ) * 1)))) =
    wGoctadE26pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE26pGT12Labs,
        wGoctadE26pGT12Nums, 2048), (wGoctadE26pGT13Labs, wGoctadE26pGT13Nums, 1000)])) : ℚ) := by
  decide +kernel

/-- The odd short part equals the odd self part of the target (group checks, no predicted values).
-/
theorem wGoctadE26p_ha : (oddWZ 64 true wGoctadE26pHXn wGoctadE26pW : ℚ) / (2 * ((tensorWordDenAll
    wGoctadE26pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)))) =
    wGoctadE26pW.sden * (selfOddP wGoctadE26pW : ℚ) :=
  oddPart_of_groups 64 true wGoctadE26pHXn wGoctadE26pW _ wGoctadE26p_WshG wGoctadE26p_sd
      ((tensorWordDenAll wGoctadE26pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) (by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl
    exacts [wGoctadE26p_og0, wGoctadE26p_og1, wGoctadE26p_og2, wGoctadE26p_og3])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
