/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE10T27nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE10T27nTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (odd short terms) of the identification Eighth[14]- <-> Tenth[55]- (record
goctad:E10@T27-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target short block as packed chunks, in groups. -/
theorem wGoctadE10T27n_WshG : wGoctadE10T27nW.sh = ShortData.ofList [OctadDense.octChunkTerms
    [(wGoctadE10T27nGT0Labs, wGoctadE10T27nGT0Nums, 2048), (wGoctadE10T27nGT1Labs,
    wGoctadE10T27nGT1Nums, 2048), (wGoctadE10T27nGT2Labs, wGoctadE10T27nGT2Nums, 2048),
    (wGoctadE10T27nGT3Labs, wGoctadE10T27nGT3Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadE10T27nGT4Labs, wGoctadE10T27nGT4Nums, 2048), (wGoctadE10T27nGT5Labs,
    wGoctadE10T27nGT5Nums, 2048), (wGoctadE10T27nGT6Labs, wGoctadE10T27nGT6Nums, 2048),
    (wGoctadE10T27nGT7Labs, wGoctadE10T27nGT7Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadE10T27nGT8Labs, wGoctadE10T27nGT8Nums, 2048), (wGoctadE10T27nGT9Labs,
    wGoctadE10T27nGT9Nums, 2048), (wGoctadE10T27nGT10Labs, wGoctadE10T27nGT10Nums, 2048),
    (wGoctadE10T27nGT11Labs, wGoctadE10T27nGT11Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadE10T27nGT12Labs, wGoctadE10T27nGT12Nums, 2048), (wGoctadE10T27nGT13Labs,
    wGoctadE10T27nGT13Nums, 2048), (wGoctadE10T27nGT14Labs, wGoctadE10T27nGT14Nums, 2048),
    (wGoctadE10T27nGT15Labs, wGoctadE10T27nGT15Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadE10T27nGT16Labs, wGoctadE10T27nGT16Nums, 2048), (wGoctadE10T27nGT17Labs,
    wGoctadE10T27nGT17Nums, 2048), (wGoctadE10T27nGT18Labs, wGoctadE10T27nGT18Nums, 2048),
    (wGoctadE10T27nGT19Labs, wGoctadE10T27nGT19Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadE10T27nGT20Labs, wGoctadE10T27nGT20Nums, 2048), (wGoctadE10T27nGT21Labs,
    wGoctadE10T27nGT21Nums, 2048), (wGoctadE10T27nGT22Labs, wGoctadE10T27nGT22Nums,
    1026)]].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, OctadDense.octChunkTerms,
    List.append_assoc]
  rfl

set_option maxRecDepth 100000 in
/-- The odd labels of the target are distinct. -/
theorem wGoctadE10T27n_sd : labDistinct wGoctadE10T27nW.sh.odd 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 0: equal to the odd self part of the group. -/
theorem wGoctadE10T27n_og0 : (oddSumF 64 false wGoctadE10T27nHX0 (OctadDense.octChunkTerms
    [(wGoctadE10T27nGT0Labs, wGoctadE10T27nGT0Nums, 2048), (wGoctadE10T27nGT1Labs,
    wGoctadE10T27nGT1Nums, 2048), (wGoctadE10T27nGT2Labs, wGoctadE10T27nGT2Nums, 2048),
    (wGoctadE10T27nGT3Labs, wGoctadE10T27nGT3Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGoctadE10T27nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 25)) =
    wGoctadE10T27nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE10T27nGT0Labs,
        wGoctadE10T27nGT0Nums, 2048), (wGoctadE10T27nGT1Labs, wGoctadE10T27nGT1Nums, 2048),
        (wGoctadE10T27nGT2Labs, wGoctadE10T27nGT2Nums, 2048), (wGoctadE10T27nGT3Labs,
        wGoctadE10T27nGT3Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 1: equal to the odd self part of the group. -/
theorem wGoctadE10T27n_og1 : (oddSumF 64 false wGoctadE10T27nHX0 (OctadDense.octChunkTerms
    [(wGoctadE10T27nGT4Labs, wGoctadE10T27nGT4Nums, 2048), (wGoctadE10T27nGT5Labs,
    wGoctadE10T27nGT5Nums, 2048), (wGoctadE10T27nGT6Labs, wGoctadE10T27nGT6Nums, 2048),
    (wGoctadE10T27nGT7Labs, wGoctadE10T27nGT7Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGoctadE10T27nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 25)) =
    wGoctadE10T27nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE10T27nGT4Labs,
        wGoctadE10T27nGT4Nums, 2048), (wGoctadE10T27nGT5Labs, wGoctadE10T27nGT5Nums, 2048),
        (wGoctadE10T27nGT6Labs, wGoctadE10T27nGT6Nums, 2048), (wGoctadE10T27nGT7Labs,
        wGoctadE10T27nGT7Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 2: equal to the odd self part of the group. -/
theorem wGoctadE10T27n_og2 : (oddSumF 64 false wGoctadE10T27nHX0 (OctadDense.octChunkTerms
    [(wGoctadE10T27nGT8Labs, wGoctadE10T27nGT8Nums, 2048), (wGoctadE10T27nGT9Labs,
    wGoctadE10T27nGT9Nums, 2048), (wGoctadE10T27nGT10Labs, wGoctadE10T27nGT10Nums, 2048),
    (wGoctadE10T27nGT11Labs, wGoctadE10T27nGT11Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGoctadE10T27nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 25)) =
    wGoctadE10T27nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE10T27nGT8Labs,
        wGoctadE10T27nGT8Nums, 2048), (wGoctadE10T27nGT9Labs, wGoctadE10T27nGT9Nums, 2048),
        (wGoctadE10T27nGT10Labs, wGoctadE10T27nGT10Nums, 2048), (wGoctadE10T27nGT11Labs,
        wGoctadE10T27nGT11Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 3: equal to the odd self part of the group. -/
theorem wGoctadE10T27n_og3 : (oddSumF 64 false wGoctadE10T27nHX0 (OctadDense.octChunkTerms
    [(wGoctadE10T27nGT12Labs, wGoctadE10T27nGT12Nums, 2048), (wGoctadE10T27nGT13Labs,
    wGoctadE10T27nGT13Nums, 2048), (wGoctadE10T27nGT14Labs, wGoctadE10T27nGT14Nums, 2048),
    (wGoctadE10T27nGT15Labs, wGoctadE10T27nGT15Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGoctadE10T27nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 25)) =
    wGoctadE10T27nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE10T27nGT12Labs,
        wGoctadE10T27nGT12Nums, 2048), (wGoctadE10T27nGT13Labs, wGoctadE10T27nGT13Nums, 2048),
        (wGoctadE10T27nGT14Labs, wGoctadE10T27nGT14Nums, 2048), (wGoctadE10T27nGT15Labs,
        wGoctadE10T27nGT15Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 4: equal to the odd self part of the group. -/
theorem wGoctadE10T27n_og4 : (oddSumF 64 false wGoctadE10T27nHX0 (OctadDense.octChunkTerms
    [(wGoctadE10T27nGT16Labs, wGoctadE10T27nGT16Nums, 2048), (wGoctadE10T27nGT17Labs,
    wGoctadE10T27nGT17Nums, 2048), (wGoctadE10T27nGT18Labs, wGoctadE10T27nGT18Nums, 2048),
    (wGoctadE10T27nGT19Labs, wGoctadE10T27nGT19Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGoctadE10T27nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 25)) =
    wGoctadE10T27nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE10T27nGT16Labs,
        wGoctadE10T27nGT16Nums, 2048), (wGoctadE10T27nGT17Labs, wGoctadE10T27nGT17Nums, 2048),
        (wGoctadE10T27nGT18Labs, wGoctadE10T27nGT18Nums, 2048), (wGoctadE10T27nGT19Labs,
        wGoctadE10T27nGT19Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 5: equal to the odd self part of the group. -/
theorem wGoctadE10T27n_og5 : (oddSumF 64 false wGoctadE10T27nHX0 (OctadDense.octChunkTerms
    [(wGoctadE10T27nGT20Labs, wGoctadE10T27nGT20Nums, 2048), (wGoctadE10T27nGT21Labs,
    wGoctadE10T27nGT21Nums, 2048), (wGoctadE10T27nGT22Labs, wGoctadE10T27nGT22Nums, 1026)]) : ℚ) /
    (2 * (((tensorWordDenAll wGoctadE10T27nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)))
    / 2 ^ 25)) =
    wGoctadE10T27nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE10T27nGT20Labs,
        wGoctadE10T27nGT20Nums, 2048), (wGoctadE10T27nGT21Labs, wGoctadE10T27nGT21Nums, 2048),
        (wGoctadE10T27nGT22Labs, wGoctadE10T27nGT22Nums, 1026)])) : ℚ) := by
  decide +kernel

/-- The odd short part equals the odd self part of the target (group checks, no predicted values).
-/
theorem wGoctadE10T27n_ha : (oddWZ 64 false wGoctadE10T27nHX0 wGoctadE10T27nW : ℚ) / (2 *
    (((tensorWordDenAll wGoctadE10T27nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2
    ^ 25)) =
    wGoctadE10T27nW.sden * (selfOddP wGoctadE10T27nW : ℚ) :=
  oddPart_of_groups 64 false wGoctadE10T27nHX0 wGoctadE10T27nW _ wGoctadE10T27n_WshG
      wGoctadE10T27n_sd (((tensorWordDenAll wGoctadE10T27nH : ℚ) * (2 * ((tensorWordDenAll
      srcEighthH : ℚ) * 1))) / 2 ^ 25) (by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [wGoctadE10T27n_og0, wGoctadE10T27n_og1, wGoctadE10T27n_og2, wGoctadE10T27n_og3,
        wGoctadE10T27n_og4, wGoctadE10T27n_og5])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
