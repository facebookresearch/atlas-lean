/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE33T32pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE33T32pTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (odd short terms) of the identification Eighth[46]+ <-> Tenth[46]+ (record
goctad:E33@T32+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target short block as packed chunks, in groups. -/
theorem wGoctadE33T32p_WshG : wGoctadE33T32pW.sh = ShortData.ofList [OctadDense.octChunkTerms
    [(wGoctadE33T32pGT0Labs, wGoctadE33T32pGT0Nums, 2048), (wGoctadE33T32pGT1Labs,
    wGoctadE33T32pGT1Nums, 2048), (wGoctadE33T32pGT2Labs, wGoctadE33T32pGT2Nums, 2048),
    (wGoctadE33T32pGT3Labs, wGoctadE33T32pGT3Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadE33T32pGT4Labs, wGoctadE33T32pGT4Nums, 2048), (wGoctadE33T32pGT5Labs,
    wGoctadE33T32pGT5Nums, 2048), (wGoctadE33T32pGT6Labs, wGoctadE33T32pGT6Nums, 2048),
    (wGoctadE33T32pGT7Labs, wGoctadE33T32pGT7Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadE33T32pGT8Labs, wGoctadE33T32pGT8Nums, 2048), (wGoctadE33T32pGT9Labs,
    wGoctadE33T32pGT9Nums, 2048), (wGoctadE33T32pGT10Labs, wGoctadE33T32pGT10Nums, 2048),
    (wGoctadE33T32pGT11Labs, wGoctadE33T32pGT11Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadE33T32pGT12Labs, wGoctadE33T32pGT12Nums, 2048), (wGoctadE33T32pGT13Labs,
    wGoctadE33T32pGT13Nums, 2048), (wGoctadE33T32pGT14Labs, wGoctadE33T32pGT14Nums, 2048),
    (wGoctadE33T32pGT15Labs, wGoctadE33T32pGT15Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadE33T32pGT16Labs, wGoctadE33T32pGT16Nums, 2048), (wGoctadE33T32pGT17Labs,
    wGoctadE33T32pGT17Nums, 2048), (wGoctadE33T32pGT18Labs, wGoctadE33T32pGT18Nums, 2048),
    (wGoctadE33T32pGT19Labs, wGoctadE33T32pGT19Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadE33T32pGT20Labs, wGoctadE33T32pGT20Nums, 2048), (wGoctadE33T32pGT21Labs,
    wGoctadE33T32pGT21Nums, 2048), (wGoctadE33T32pGT22Labs, wGoctadE33T32pGT22Nums,
    1026)]].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, OctadDense.octChunkTerms,
    List.append_assoc]
  rfl

set_option maxRecDepth 100000 in
/-- The odd labels of the target are distinct. -/
theorem wGoctadE33T32p_sd : labDistinct wGoctadE33T32pW.sh.odd 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 0: equal to the odd self part of the group. -/
theorem wGoctadE33T32p_og0 : (oddSumF 80 true wGoctadE33T32pHX0 (OctadDense.octChunkTerms
    [(wGoctadE33T32pGT0Labs, wGoctadE33T32pGT0Nums, 2048), (wGoctadE33T32pGT1Labs,
    wGoctadE33T32pGT1Nums, 2048), (wGoctadE33T32pGT2Labs, wGoctadE33T32pGT2Nums, 2048),
    (wGoctadE33T32pGT3Labs, wGoctadE33T32pGT3Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGoctadE33T32pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 37)) =
    wGoctadE33T32pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE33T32pGT0Labs,
        wGoctadE33T32pGT0Nums, 2048), (wGoctadE33T32pGT1Labs, wGoctadE33T32pGT1Nums, 2048),
        (wGoctadE33T32pGT2Labs, wGoctadE33T32pGT2Nums, 2048), (wGoctadE33T32pGT3Labs,
        wGoctadE33T32pGT3Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 1: equal to the odd self part of the group. -/
theorem wGoctadE33T32p_og1 : (oddSumF 80 true wGoctadE33T32pHX0 (OctadDense.octChunkTerms
    [(wGoctadE33T32pGT4Labs, wGoctadE33T32pGT4Nums, 2048), (wGoctadE33T32pGT5Labs,
    wGoctadE33T32pGT5Nums, 2048), (wGoctadE33T32pGT6Labs, wGoctadE33T32pGT6Nums, 2048),
    (wGoctadE33T32pGT7Labs, wGoctadE33T32pGT7Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGoctadE33T32pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 37)) =
    wGoctadE33T32pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE33T32pGT4Labs,
        wGoctadE33T32pGT4Nums, 2048), (wGoctadE33T32pGT5Labs, wGoctadE33T32pGT5Nums, 2048),
        (wGoctadE33T32pGT6Labs, wGoctadE33T32pGT6Nums, 2048), (wGoctadE33T32pGT7Labs,
        wGoctadE33T32pGT7Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 2: equal to the odd self part of the group. -/
theorem wGoctadE33T32p_og2 : (oddSumF 80 true wGoctadE33T32pHX0 (OctadDense.octChunkTerms
    [(wGoctadE33T32pGT8Labs, wGoctadE33T32pGT8Nums, 2048), (wGoctadE33T32pGT9Labs,
    wGoctadE33T32pGT9Nums, 2048), (wGoctadE33T32pGT10Labs, wGoctadE33T32pGT10Nums, 2048),
    (wGoctadE33T32pGT11Labs, wGoctadE33T32pGT11Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGoctadE33T32pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 37)) =
    wGoctadE33T32pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE33T32pGT8Labs,
        wGoctadE33T32pGT8Nums, 2048), (wGoctadE33T32pGT9Labs, wGoctadE33T32pGT9Nums, 2048),
        (wGoctadE33T32pGT10Labs, wGoctadE33T32pGT10Nums, 2048), (wGoctadE33T32pGT11Labs,
        wGoctadE33T32pGT11Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 3: equal to the odd self part of the group. -/
theorem wGoctadE33T32p_og3 : (oddSumF 80 true wGoctadE33T32pHX0 (OctadDense.octChunkTerms
    [(wGoctadE33T32pGT12Labs, wGoctadE33T32pGT12Nums, 2048), (wGoctadE33T32pGT13Labs,
    wGoctadE33T32pGT13Nums, 2048), (wGoctadE33T32pGT14Labs, wGoctadE33T32pGT14Nums, 2048),
    (wGoctadE33T32pGT15Labs, wGoctadE33T32pGT15Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGoctadE33T32pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 37)) =
    wGoctadE33T32pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE33T32pGT12Labs,
        wGoctadE33T32pGT12Nums, 2048), (wGoctadE33T32pGT13Labs, wGoctadE33T32pGT13Nums, 2048),
        (wGoctadE33T32pGT14Labs, wGoctadE33T32pGT14Nums, 2048), (wGoctadE33T32pGT15Labs,
        wGoctadE33T32pGT15Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 4: equal to the odd self part of the group. -/
theorem wGoctadE33T32p_og4 : (oddSumF 80 true wGoctadE33T32pHX0 (OctadDense.octChunkTerms
    [(wGoctadE33T32pGT16Labs, wGoctadE33T32pGT16Nums, 2048), (wGoctadE33T32pGT17Labs,
    wGoctadE33T32pGT17Nums, 2048), (wGoctadE33T32pGT18Labs, wGoctadE33T32pGT18Nums, 2048),
    (wGoctadE33T32pGT19Labs, wGoctadE33T32pGT19Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGoctadE33T32pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 37)) =
    wGoctadE33T32pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE33T32pGT16Labs,
        wGoctadE33T32pGT16Nums, 2048), (wGoctadE33T32pGT17Labs, wGoctadE33T32pGT17Nums, 2048),
        (wGoctadE33T32pGT18Labs, wGoctadE33T32pGT18Nums, 2048), (wGoctadE33T32pGT19Labs,
        wGoctadE33T32pGT19Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 5: equal to the odd self part of the group. -/
theorem wGoctadE33T32p_og5 : (oddSumF 80 true wGoctadE33T32pHX0 (OctadDense.octChunkTerms
    [(wGoctadE33T32pGT20Labs, wGoctadE33T32pGT20Nums, 2048), (wGoctadE33T32pGT21Labs,
    wGoctadE33T32pGT21Nums, 2048), (wGoctadE33T32pGT22Labs, wGoctadE33T32pGT22Nums, 1026)]) : ℚ) /
    (2 * (((tensorWordDenAll wGoctadE33T32pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)))
    / 2 ^ 37)) =
    wGoctadE33T32pW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE33T32pGT20Labs,
        wGoctadE33T32pGT20Nums, 2048), (wGoctadE33T32pGT21Labs, wGoctadE33T32pGT21Nums, 2048),
        (wGoctadE33T32pGT22Labs, wGoctadE33T32pGT22Nums, 1026)])) : ℚ) := by
  decide +kernel

/-- The odd short part equals the odd self part of the target (group checks, no predicted values).
-/
theorem wGoctadE33T32p_ha : (oddWZ 80 true wGoctadE33T32pHX0 wGoctadE33T32pW : ℚ) / (2 *
    (((tensorWordDenAll wGoctadE33T32pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2
    ^ 37)) =
    wGoctadE33T32pW.sden * (selfOddP wGoctadE33T32pW : ℚ) :=
  oddPart_of_groups 80 true wGoctadE33T32pHX0 wGoctadE33T32pW _ wGoctadE33T32p_WshG
      wGoctadE33T32p_sd (((tensorWordDenAll wGoctadE33T32pH : ℚ) * (2 * ((tensorWordDenAll
      srcEighthH : ℚ) * 1))) / 2 ^ 37) (by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [wGoctadE33T32p_og0, wGoctadE33T32p_og1, wGoctadE33T32p_og2, wGoctadE33T32p_og3,
        wGoctadE33T32p_og4, wGoctadE33T32p_og5])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
