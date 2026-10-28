/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c12pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c12pTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (odd short terms) of the identification Root8[10]- <-> Seventh[19]+ (record
gforest:S7c12+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target short block as packed chunks, in groups. -/
theorem wGforestS7c12p_WshG : wGforestS7c12pW.sh = ShortData.ofList [OctadDense.octChunkTerms
    [(wGforestS7c12pGT0Labs, wGforestS7c12pGT0Nums, 2048), (wGforestS7c12pGT1Labs,
    wGforestS7c12pGT1Nums, 2048), (wGforestS7c12pGT2Labs, wGforestS7c12pGT2Nums, 2048),
    (wGforestS7c12pGT3Labs, wGforestS7c12pGT3Nums, 2048)], OctadDense.octChunkTerms
    [(wGforestS7c12pGT4Labs, wGforestS7c12pGT4Nums, 2048), (wGforestS7c12pGT5Labs,
    wGforestS7c12pGT5Nums, 2048), (wGforestS7c12pGT6Labs, wGforestS7c12pGT6Nums, 2048),
    (wGforestS7c12pGT7Labs, wGforestS7c12pGT7Nums, 2048)], OctadDense.octChunkTerms
    [(wGforestS7c12pGT8Labs, wGforestS7c12pGT8Nums, 2048), (wGforestS7c12pGT9Labs,
    wGforestS7c12pGT9Nums, 2048), (wGforestS7c12pGT10Labs, wGforestS7c12pGT10Nums, 2048),
    (wGforestS7c12pGT11Labs, wGforestS7c12pGT11Nums, 2048)], OctadDense.octChunkTerms
    [(wGforestS7c12pGT12Labs, wGforestS7c12pGT12Nums, 2048), (wGforestS7c12pGT13Labs,
    wGforestS7c12pGT13Nums, 2048), (wGforestS7c12pGT14Labs, wGforestS7c12pGT14Nums, 2048),
    (wGforestS7c12pGT15Labs, wGforestS7c12pGT15Nums, 2048)], OctadDense.octChunkTerms
    [(wGforestS7c12pGT16Labs, wGforestS7c12pGT16Nums, 808)]].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, OctadDense.octChunkTerms,
    List.append_assoc]
  rfl

set_option maxRecDepth 100000 in
/-- The odd labels of the target are distinct. -/
theorem wGforestS7c12p_sd : labDistinct wGforestS7c12pW.sh.odd 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 0: equal to the odd self part of the group. -/
theorem wGforestS7c12p_og0 : (oddSumF 64 true wGforestS7c12pHX0 (OctadDense.octChunkTerms
    [(wGforestS7c12pGT0Labs, wGforestS7c12pGT0Nums, 2048), (wGforestS7c12pGT1Labs,
    wGforestS7c12pGT1Nums, 2048), (wGforestS7c12pGT2Labs, wGforestS7c12pGT2Nums, 2048),
    (wGforestS7c12pGT3Labs, wGforestS7c12pGT3Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGforestS7c12pH : ℚ) * srcSeventhD0) / 2 ^ 20)) =
    wGforestS7c12pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGforestS7c12pGT0Labs,
        wGforestS7c12pGT0Nums, 2048), (wGforestS7c12pGT1Labs, wGforestS7c12pGT1Nums, 2048),
        (wGforestS7c12pGT2Labs, wGforestS7c12pGT2Nums, 2048), (wGforestS7c12pGT3Labs,
        wGforestS7c12pGT3Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 1: equal to the odd self part of the group. -/
theorem wGforestS7c12p_og1 : (oddSumF 64 true wGforestS7c12pHX0 (OctadDense.octChunkTerms
    [(wGforestS7c12pGT4Labs, wGforestS7c12pGT4Nums, 2048), (wGforestS7c12pGT5Labs,
    wGforestS7c12pGT5Nums, 2048), (wGforestS7c12pGT6Labs, wGforestS7c12pGT6Nums, 2048),
    (wGforestS7c12pGT7Labs, wGforestS7c12pGT7Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGforestS7c12pH : ℚ) * srcSeventhD0) / 2 ^ 20)) =
    wGforestS7c12pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGforestS7c12pGT4Labs,
        wGforestS7c12pGT4Nums, 2048), (wGforestS7c12pGT5Labs, wGforestS7c12pGT5Nums, 2048),
        (wGforestS7c12pGT6Labs, wGforestS7c12pGT6Nums, 2048), (wGforestS7c12pGT7Labs,
        wGforestS7c12pGT7Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 2: equal to the odd self part of the group. -/
theorem wGforestS7c12p_og2 : (oddSumF 64 true wGforestS7c12pHX0 (OctadDense.octChunkTerms
    [(wGforestS7c12pGT8Labs, wGforestS7c12pGT8Nums, 2048), (wGforestS7c12pGT9Labs,
    wGforestS7c12pGT9Nums, 2048), (wGforestS7c12pGT10Labs, wGforestS7c12pGT10Nums, 2048),
    (wGforestS7c12pGT11Labs, wGforestS7c12pGT11Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGforestS7c12pH : ℚ) * srcSeventhD0) / 2 ^ 20)) =
    wGforestS7c12pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGforestS7c12pGT8Labs,
        wGforestS7c12pGT8Nums, 2048), (wGforestS7c12pGT9Labs, wGforestS7c12pGT9Nums, 2048),
        (wGforestS7c12pGT10Labs, wGforestS7c12pGT10Nums, 2048), (wGforestS7c12pGT11Labs,
        wGforestS7c12pGT11Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 3: equal to the odd self part of the group. -/
theorem wGforestS7c12p_og3 : (oddSumF 64 true wGforestS7c12pHX0 (OctadDense.octChunkTerms
    [(wGforestS7c12pGT12Labs, wGforestS7c12pGT12Nums, 2048), (wGforestS7c12pGT13Labs,
    wGforestS7c12pGT13Nums, 2048), (wGforestS7c12pGT14Labs, wGforestS7c12pGT14Nums, 2048),
    (wGforestS7c12pGT15Labs, wGforestS7c12pGT15Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGforestS7c12pH : ℚ) * srcSeventhD0) / 2 ^ 20)) =
    wGforestS7c12pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGforestS7c12pGT12Labs,
        wGforestS7c12pGT12Nums, 2048), (wGforestS7c12pGT13Labs, wGforestS7c12pGT13Nums, 2048),
        (wGforestS7c12pGT14Labs, wGforestS7c12pGT14Nums, 2048), (wGforestS7c12pGT15Labs,
        wGforestS7c12pGT15Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 4: equal to the odd self part of the group. -/
theorem wGforestS7c12p_og4 : (oddSumF 64 true wGforestS7c12pHX0 (OctadDense.octChunkTerms
    [(wGforestS7c12pGT16Labs, wGforestS7c12pGT16Nums, 808)]) : ℚ) / (2 * (((tensorWordDenAll
    wGforestS7c12pH : ℚ) * srcSeventhD0) / 2 ^ 20)) =
    wGforestS7c12pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGforestS7c12pGT16Labs,
        wGforestS7c12pGT16Nums, 808)])) : ℚ) := by
  decide +kernel

/-- The odd short part equals the odd self part of the target (group checks, no predicted values).
-/
theorem wGforestS7c12p_ha : (oddWZ 64 true wGforestS7c12pHX0 wGforestS7c12pW : ℚ) / (2 *
    (((tensorWordDenAll wGforestS7c12pH : ℚ) * srcSeventhD0) / 2 ^ 20)) =
    wGforestS7c12pW.sden * (selfOddP wGforestS7c12pW : ℚ) :=
  oddPart_of_groups 64 true wGforestS7c12pHX0 wGforestS7c12pW _ wGforestS7c12p_WshG
      wGforestS7c12p_sd (((tensorWordDenAll wGforestS7c12pH : ℚ) * srcSeventhD0) / 2 ^ 20) (by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl
    exacts [wGforestS7c12p_og0, wGforestS7c12p_og1, wGforestS7c12p_og2, wGforestS7c12p_og3,
        wGforestS7c12p_og4])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
