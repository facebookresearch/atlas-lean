/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c14pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c14pTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (odd short terms) of the identification Eighth[27]+ <-> Seventh[22]+ (record
gforest:S7c14+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target short block as packed chunks, in groups. -/
theorem wGforestS7c14p_WshG : wGforestS7c14pW.sh = ShortData.ofList [OctadDense.octChunkTerms
    [(wGforestS7c14pGT0Labs, wGforestS7c14pGT0Nums, 2048), (wGforestS7c14pGT1Labs,
    wGforestS7c14pGT1Nums, 2048), (wGforestS7c14pGT2Labs, wGforestS7c14pGT2Nums, 2048),
    (wGforestS7c14pGT3Labs, wGforestS7c14pGT3Nums, 2048)], OctadDense.octChunkTerms
    [(wGforestS7c14pGT4Labs, wGforestS7c14pGT4Nums, 2048), (wGforestS7c14pGT5Labs,
    wGforestS7c14pGT5Nums, 2048), (wGforestS7c14pGT6Labs, wGforestS7c14pGT6Nums, 2048),
    (wGforestS7c14pGT7Labs, wGforestS7c14pGT7Nums, 2048)], OctadDense.octChunkTerms
    [(wGforestS7c14pGT8Labs, wGforestS7c14pGT8Nums, 2048), (wGforestS7c14pGT9Labs,
    wGforestS7c14pGT9Nums, 2048), (wGforestS7c14pGT10Labs, wGforestS7c14pGT10Nums, 2048),
    (wGforestS7c14pGT11Labs, wGforestS7c14pGT11Nums, 2048)], OctadDense.octChunkTerms
    [(wGforestS7c14pGT12Labs, wGforestS7c14pGT12Nums, 2048), (wGforestS7c14pGT13Labs,
    wGforestS7c14pGT13Nums, 2048), (wGforestS7c14pGT14Labs, wGforestS7c14pGT14Nums, 2048),
    (wGforestS7c14pGT15Labs, wGforestS7c14pGT15Nums, 2048)], OctadDense.octChunkTerms
    [(wGforestS7c14pGT16Labs, wGforestS7c14pGT16Nums, 2048), (wGforestS7c14pGT17Labs,
    wGforestS7c14pGT17Nums, 2048), (wGforestS7c14pGT18Labs, wGforestS7c14pGT18Nums, 2048),
    (wGforestS7c14pGT19Labs, wGforestS7c14pGT19Nums, 2048)], OctadDense.octChunkTerms
    [(wGforestS7c14pGT20Labs, wGforestS7c14pGT20Nums, 2048), (wGforestS7c14pGT21Labs,
    wGforestS7c14pGT21Nums, 668)]].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, OctadDense.octChunkTerms,
    List.append_assoc]
  rfl

set_option maxRecDepth 100000 in
/-- The odd labels of the target are distinct. -/
theorem wGforestS7c14p_sd : labDistinct wGforestS7c14pW.sh.odd 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 0: equal to the odd self part of the group. -/
theorem wGforestS7c14p_og0 : (oddSumF 64 true wGforestS7c14pHX0 (OctadDense.octChunkTerms
    [(wGforestS7c14pGT0Labs, wGforestS7c14pGT0Nums, 2048), (wGforestS7c14pGT1Labs,
    wGforestS7c14pGT1Nums, 2048), (wGforestS7c14pGT2Labs, wGforestS7c14pGT2Nums, 2048),
    (wGforestS7c14pGT3Labs, wGforestS7c14pGT3Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGforestS7c14pH : ℚ) * srcSeventhD0) / 2 ^ 20)) =
    wGforestS7c14pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGforestS7c14pGT0Labs,
        wGforestS7c14pGT0Nums, 2048), (wGforestS7c14pGT1Labs, wGforestS7c14pGT1Nums, 2048),
        (wGforestS7c14pGT2Labs, wGforestS7c14pGT2Nums, 2048), (wGforestS7c14pGT3Labs,
        wGforestS7c14pGT3Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 1: equal to the odd self part of the group. -/
theorem wGforestS7c14p_og1 : (oddSumF 64 true wGforestS7c14pHX0 (OctadDense.octChunkTerms
    [(wGforestS7c14pGT4Labs, wGforestS7c14pGT4Nums, 2048), (wGforestS7c14pGT5Labs,
    wGforestS7c14pGT5Nums, 2048), (wGforestS7c14pGT6Labs, wGforestS7c14pGT6Nums, 2048),
    (wGforestS7c14pGT7Labs, wGforestS7c14pGT7Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGforestS7c14pH : ℚ) * srcSeventhD0) / 2 ^ 20)) =
    wGforestS7c14pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGforestS7c14pGT4Labs,
        wGforestS7c14pGT4Nums, 2048), (wGforestS7c14pGT5Labs, wGforestS7c14pGT5Nums, 2048),
        (wGforestS7c14pGT6Labs, wGforestS7c14pGT6Nums, 2048), (wGforestS7c14pGT7Labs,
        wGforestS7c14pGT7Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 2: equal to the odd self part of the group. -/
theorem wGforestS7c14p_og2 : (oddSumF 64 true wGforestS7c14pHX0 (OctadDense.octChunkTerms
    [(wGforestS7c14pGT8Labs, wGforestS7c14pGT8Nums, 2048), (wGforestS7c14pGT9Labs,
    wGforestS7c14pGT9Nums, 2048), (wGforestS7c14pGT10Labs, wGforestS7c14pGT10Nums, 2048),
    (wGforestS7c14pGT11Labs, wGforestS7c14pGT11Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGforestS7c14pH : ℚ) * srcSeventhD0) / 2 ^ 20)) =
    wGforestS7c14pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGforestS7c14pGT8Labs,
        wGforestS7c14pGT8Nums, 2048), (wGforestS7c14pGT9Labs, wGforestS7c14pGT9Nums, 2048),
        (wGforestS7c14pGT10Labs, wGforestS7c14pGT10Nums, 2048), (wGforestS7c14pGT11Labs,
        wGforestS7c14pGT11Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 3: equal to the odd self part of the group. -/
theorem wGforestS7c14p_og3 : (oddSumF 64 true wGforestS7c14pHX0 (OctadDense.octChunkTerms
    [(wGforestS7c14pGT12Labs, wGforestS7c14pGT12Nums, 2048), (wGforestS7c14pGT13Labs,
    wGforestS7c14pGT13Nums, 2048), (wGforestS7c14pGT14Labs, wGforestS7c14pGT14Nums, 2048),
    (wGforestS7c14pGT15Labs, wGforestS7c14pGT15Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGforestS7c14pH : ℚ) * srcSeventhD0) / 2 ^ 20)) =
    wGforestS7c14pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGforestS7c14pGT12Labs,
        wGforestS7c14pGT12Nums, 2048), (wGforestS7c14pGT13Labs, wGforestS7c14pGT13Nums, 2048),
        (wGforestS7c14pGT14Labs, wGforestS7c14pGT14Nums, 2048), (wGforestS7c14pGT15Labs,
        wGforestS7c14pGT15Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 4: equal to the odd self part of the group. -/
theorem wGforestS7c14p_og4 : (oddSumF 64 true wGforestS7c14pHX0 (OctadDense.octChunkTerms
    [(wGforestS7c14pGT16Labs, wGforestS7c14pGT16Nums, 2048), (wGforestS7c14pGT17Labs,
    wGforestS7c14pGT17Nums, 2048), (wGforestS7c14pGT18Labs, wGforestS7c14pGT18Nums, 2048),
    (wGforestS7c14pGT19Labs, wGforestS7c14pGT19Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGforestS7c14pH : ℚ) * srcSeventhD0) / 2 ^ 20)) =
    wGforestS7c14pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGforestS7c14pGT16Labs,
        wGforestS7c14pGT16Nums, 2048), (wGforestS7c14pGT17Labs, wGforestS7c14pGT17Nums, 2048),
        (wGforestS7c14pGT18Labs, wGforestS7c14pGT18Nums, 2048), (wGforestS7c14pGT19Labs,
        wGforestS7c14pGT19Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 5: equal to the odd self part of the group. -/
theorem wGforestS7c14p_og5 : (oddSumF 64 true wGforestS7c14pHX0 (OctadDense.octChunkTerms
    [(wGforestS7c14pGT20Labs, wGforestS7c14pGT20Nums, 2048), (wGforestS7c14pGT21Labs,
    wGforestS7c14pGT21Nums, 668)]) : ℚ) / (2 * (((tensorWordDenAll wGforestS7c14pH : ℚ) *
    srcSeventhD0) / 2 ^ 20)) =
    wGforestS7c14pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGforestS7c14pGT20Labs,
        wGforestS7c14pGT20Nums, 2048), (wGforestS7c14pGT21Labs, wGforestS7c14pGT21Nums, 668)])) :
        ℚ) := by
  decide +kernel

/-- The odd short part equals the odd self part of the target (group checks, no predicted values).
-/
theorem wGforestS7c14p_ha : (oddWZ 64 true wGforestS7c14pHX0 wGforestS7c14pW : ℚ) / (2 *
    (((tensorWordDenAll wGforestS7c14pH : ℚ) * srcSeventhD0) / 2 ^ 20)) =
    wGforestS7c14pW.sden * (selfOddP wGforestS7c14pW : ℚ) :=
  oddPart_of_groups 64 true wGforestS7c14pHX0 wGforestS7c14pW _ wGforestS7c14p_WshG
      wGforestS7c14p_sd (((tensorWordDenAll wGforestS7c14pH : ℚ) * srcSeventhD0) / 2 ^ 20) (by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [wGforestS7c14p_og0, wGforestS7c14p_og1, wGforestS7c14p_og2, wGforestS7c14p_og3,
        wGforestS7c14p_og4, wGforestS7c14p_og5])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
