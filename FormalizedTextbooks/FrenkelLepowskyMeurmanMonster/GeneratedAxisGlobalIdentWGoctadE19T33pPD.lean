/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE19T33pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE19T33pTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (odd short terms) of the identification Eighth[24]+ <-> Tenth[61]+ (record
goctad:E19@T33+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target short block as packed chunks, in groups. -/
theorem wGoctadE19T33p_WshG : wGoctadE19T33pW.sh = ShortData.ofList [OctadDense.octChunkTerms
    [(wGoctadE19T33pGT0Labs, wGoctadE19T33pGT0Nums, 2048), (wGoctadE19T33pGT1Labs,
    wGoctadE19T33pGT1Nums, 2048), (wGoctadE19T33pGT2Labs, wGoctadE19T33pGT2Nums, 2048),
    (wGoctadE19T33pGT3Labs, wGoctadE19T33pGT3Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadE19T33pGT4Labs, wGoctadE19T33pGT4Nums, 2048), (wGoctadE19T33pGT5Labs,
    wGoctadE19T33pGT5Nums, 2048), (wGoctadE19T33pGT6Labs, wGoctadE19T33pGT6Nums, 2048),
    (wGoctadE19T33pGT7Labs, wGoctadE19T33pGT7Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadE19T33pGT8Labs, wGoctadE19T33pGT8Nums, 2048), (wGoctadE19T33pGT9Labs,
    wGoctadE19T33pGT9Nums, 2048), (wGoctadE19T33pGT10Labs, wGoctadE19T33pGT10Nums, 2048),
    (wGoctadE19T33pGT11Labs, wGoctadE19T33pGT11Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadE19T33pGT12Labs, wGoctadE19T33pGT12Nums, 2048), (wGoctadE19T33pGT13Labs,
    wGoctadE19T33pGT13Nums, 2048), (wGoctadE19T33pGT14Labs, wGoctadE19T33pGT14Nums, 2048),
    (wGoctadE19T33pGT15Labs, wGoctadE19T33pGT15Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadE19T33pGT16Labs, wGoctadE19T33pGT16Nums, 2048), (wGoctadE19T33pGT17Labs,
    wGoctadE19T33pGT17Nums, 2048), (wGoctadE19T33pGT18Labs, wGoctadE19T33pGT18Nums, 2048),
    (wGoctadE19T33pGT19Labs, wGoctadE19T33pGT19Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadE19T33pGT20Labs, wGoctadE19T33pGT20Nums, 2048), (wGoctadE19T33pGT21Labs,
    wGoctadE19T33pGT21Nums, 2048), (wGoctadE19T33pGT22Labs, wGoctadE19T33pGT22Nums,
    1026)]].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, OctadDense.octChunkTerms,
    List.append_assoc]
  rfl

set_option maxRecDepth 100000 in
/-- The odd labels of the target are distinct. -/
theorem wGoctadE19T33p_sd : labDistinct wGoctadE19T33pW.sh.odd 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 0: equal to the odd self part of the group. -/
theorem wGoctadE19T33p_og0 : (oddSumF 64 true wGoctadE19T33pHX0 (OctadDense.octChunkTerms
    [(wGoctadE19T33pGT0Labs, wGoctadE19T33pGT0Nums, 2048), (wGoctadE19T33pGT1Labs,
    wGoctadE19T33pGT1Nums, 2048), (wGoctadE19T33pGT2Labs, wGoctadE19T33pGT2Nums, 2048),
    (wGoctadE19T33pGT3Labs, wGoctadE19T33pGT3Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGoctadE19T33pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 25)) =
    wGoctadE19T33pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE19T33pGT0Labs,
        wGoctadE19T33pGT0Nums, 2048), (wGoctadE19T33pGT1Labs, wGoctadE19T33pGT1Nums, 2048),
        (wGoctadE19T33pGT2Labs, wGoctadE19T33pGT2Nums, 2048), (wGoctadE19T33pGT3Labs,
        wGoctadE19T33pGT3Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 1: equal to the odd self part of the group. -/
theorem wGoctadE19T33p_og1 : (oddSumF 64 true wGoctadE19T33pHX0 (OctadDense.octChunkTerms
    [(wGoctadE19T33pGT4Labs, wGoctadE19T33pGT4Nums, 2048), (wGoctadE19T33pGT5Labs,
    wGoctadE19T33pGT5Nums, 2048), (wGoctadE19T33pGT6Labs, wGoctadE19T33pGT6Nums, 2048),
    (wGoctadE19T33pGT7Labs, wGoctadE19T33pGT7Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGoctadE19T33pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 25)) =
    wGoctadE19T33pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE19T33pGT4Labs,
        wGoctadE19T33pGT4Nums, 2048), (wGoctadE19T33pGT5Labs, wGoctadE19T33pGT5Nums, 2048),
        (wGoctadE19T33pGT6Labs, wGoctadE19T33pGT6Nums, 2048), (wGoctadE19T33pGT7Labs,
        wGoctadE19T33pGT7Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 2: equal to the odd self part of the group. -/
theorem wGoctadE19T33p_og2 : (oddSumF 64 true wGoctadE19T33pHX0 (OctadDense.octChunkTerms
    [(wGoctadE19T33pGT8Labs, wGoctadE19T33pGT8Nums, 2048), (wGoctadE19T33pGT9Labs,
    wGoctadE19T33pGT9Nums, 2048), (wGoctadE19T33pGT10Labs, wGoctadE19T33pGT10Nums, 2048),
    (wGoctadE19T33pGT11Labs, wGoctadE19T33pGT11Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGoctadE19T33pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 25)) =
    wGoctadE19T33pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE19T33pGT8Labs,
        wGoctadE19T33pGT8Nums, 2048), (wGoctadE19T33pGT9Labs, wGoctadE19T33pGT9Nums, 2048),
        (wGoctadE19T33pGT10Labs, wGoctadE19T33pGT10Nums, 2048), (wGoctadE19T33pGT11Labs,
        wGoctadE19T33pGT11Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 3: equal to the odd self part of the group. -/
theorem wGoctadE19T33p_og3 : (oddSumF 64 true wGoctadE19T33pHX0 (OctadDense.octChunkTerms
    [(wGoctadE19T33pGT12Labs, wGoctadE19T33pGT12Nums, 2048), (wGoctadE19T33pGT13Labs,
    wGoctadE19T33pGT13Nums, 2048), (wGoctadE19T33pGT14Labs, wGoctadE19T33pGT14Nums, 2048),
    (wGoctadE19T33pGT15Labs, wGoctadE19T33pGT15Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGoctadE19T33pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 25)) =
    wGoctadE19T33pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE19T33pGT12Labs,
        wGoctadE19T33pGT12Nums, 2048), (wGoctadE19T33pGT13Labs, wGoctadE19T33pGT13Nums, 2048),
        (wGoctadE19T33pGT14Labs, wGoctadE19T33pGT14Nums, 2048), (wGoctadE19T33pGT15Labs,
        wGoctadE19T33pGT15Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 4: equal to the odd self part of the group. -/
theorem wGoctadE19T33p_og4 : (oddSumF 64 true wGoctadE19T33pHX0 (OctadDense.octChunkTerms
    [(wGoctadE19T33pGT16Labs, wGoctadE19T33pGT16Nums, 2048), (wGoctadE19T33pGT17Labs,
    wGoctadE19T33pGT17Nums, 2048), (wGoctadE19T33pGT18Labs, wGoctadE19T33pGT18Nums, 2048),
    (wGoctadE19T33pGT19Labs, wGoctadE19T33pGT19Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGoctadE19T33pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 25)) =
    wGoctadE19T33pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE19T33pGT16Labs,
        wGoctadE19T33pGT16Nums, 2048), (wGoctadE19T33pGT17Labs, wGoctadE19T33pGT17Nums, 2048),
        (wGoctadE19T33pGT18Labs, wGoctadE19T33pGT18Nums, 2048), (wGoctadE19T33pGT19Labs,
        wGoctadE19T33pGT19Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 5: equal to the odd self part of the group. -/
theorem wGoctadE19T33p_og5 : (oddSumF 64 true wGoctadE19T33pHX0 (OctadDense.octChunkTerms
    [(wGoctadE19T33pGT20Labs, wGoctadE19T33pGT20Nums, 2048), (wGoctadE19T33pGT21Labs,
    wGoctadE19T33pGT21Nums, 2048), (wGoctadE19T33pGT22Labs, wGoctadE19T33pGT22Nums, 1026)]) : ℚ) /
    (2 * (((tensorWordDenAll wGoctadE19T33pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)))
    / 2 ^ 25)) =
    wGoctadE19T33pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE19T33pGT20Labs,
        wGoctadE19T33pGT20Nums, 2048), (wGoctadE19T33pGT21Labs, wGoctadE19T33pGT21Nums, 2048),
        (wGoctadE19T33pGT22Labs, wGoctadE19T33pGT22Nums, 1026)])) : ℚ) := by
  decide +kernel

/-- The odd short part equals the odd self part of the target (group checks, no predicted values).
-/
theorem wGoctadE19T33p_ha : (oddWZ 64 true wGoctadE19T33pHX0 wGoctadE19T33pW : ℚ) / (2 *
    (((tensorWordDenAll wGoctadE19T33pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2
    ^ 25)) =
    wGoctadE19T33pW.sden * (selfOddP wGoctadE19T33pW : ℚ) :=
  oddPart_of_groups 64 true wGoctadE19T33pHX0 wGoctadE19T33pW _ wGoctadE19T33p_WshG
      wGoctadE19T33p_sd (((tensorWordDenAll wGoctadE19T33pH : ℚ) * (2 * ((tensorWordDenAll
      srcEighthH : ℚ) * 1))) / 2 ^ 25) (by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [wGoctadE19T33p_og0, wGoctadE19T33p_og1, wGoctadE19T33p_og2, wGoctadE19T33p_og3,
        wGoctadE19T33p_og4, wGoctadE19T33p_og5])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
