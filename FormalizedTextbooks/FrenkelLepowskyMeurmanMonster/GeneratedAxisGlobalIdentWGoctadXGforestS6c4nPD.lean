/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS6c4nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixthF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS6c4nTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (odd short terms) of the identification Sixth[8]- <-> Tenth[73]+ (record
gforest:S6c4-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target short block as packed chunks, in groups. -/
theorem wGoctadXGforestS6c4n_WshG : wGoctadXGforestS6c4nW.sh = ShortData.ofList
    [OctadDense.octChunkTerms [(wGoctadXGforestS6c4nGT0Labs, wGoctadXGforestS6c4nGT0Nums, 2048),
    (wGoctadXGforestS6c4nGT1Labs, wGoctadXGforestS6c4nGT1Nums, 2048),
    (wGoctadXGforestS6c4nGT2Labs, wGoctadXGforestS6c4nGT2Nums, 2048),
    (wGoctadXGforestS6c4nGT3Labs, wGoctadXGforestS6c4nGT3Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadXGforestS6c4nGT4Labs, wGoctadXGforestS6c4nGT4Nums, 2048),
    (wGoctadXGforestS6c4nGT5Labs, wGoctadXGforestS6c4nGT5Nums, 2048),
    (wGoctadXGforestS6c4nGT6Labs, wGoctadXGforestS6c4nGT6Nums, 2048),
    (wGoctadXGforestS6c4nGT7Labs, wGoctadXGforestS6c4nGT7Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadXGforestS6c4nGT8Labs, wGoctadXGforestS6c4nGT8Nums, 2048),
    (wGoctadXGforestS6c4nGT9Labs, wGoctadXGforestS6c4nGT9Nums, 2048),
    (wGoctadXGforestS6c4nGT10Labs, wGoctadXGforestS6c4nGT10Nums, 2048),
    (wGoctadXGforestS6c4nGT11Labs, wGoctadXGforestS6c4nGT11Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadXGforestS6c4nGT12Labs, wGoctadXGforestS6c4nGT12Nums, 2048),
    (wGoctadXGforestS6c4nGT13Labs, wGoctadXGforestS6c4nGT13Nums, 2048),
    (wGoctadXGforestS6c4nGT14Labs, wGoctadXGforestS6c4nGT14Nums, 2048),
    (wGoctadXGforestS6c4nGT15Labs, wGoctadXGforestS6c4nGT15Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadXGforestS6c4nGT16Labs, wGoctadXGforestS6c4nGT16Nums, 2048),
    (wGoctadXGforestS6c4nGT17Labs, wGoctadXGforestS6c4nGT17Nums, 2048),
    (wGoctadXGforestS6c4nGT18Labs, wGoctadXGforestS6c4nGT18Nums, 2048),
    (wGoctadXGforestS6c4nGT19Labs, wGoctadXGforestS6c4nGT19Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadXGforestS6c4nGT20Labs, wGoctadXGforestS6c4nGT20Nums, 2048),
    (wGoctadXGforestS6c4nGT21Labs, wGoctadXGforestS6c4nGT21Nums, 2048),
    (wGoctadXGforestS6c4nGT22Labs, wGoctadXGforestS6c4nGT22Nums, 1026)]].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, OctadDense.octChunkTerms,
    List.append_assoc]
  rfl

set_option maxRecDepth 100000 in
/-- The odd labels of the target are distinct. -/
theorem wGoctadXGforestS6c4n_sd : labDistinct wGoctadXGforestS6c4nW.sh.odd 0 = true := by
    decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 0: equal to the odd self part of the group. -/
theorem wGoctadXGforestS6c4n_og0 : (oddSumF 64 false wGoctadXGforestS6c4nHX0
    (OctadDense.octChunkTerms [(wGoctadXGforestS6c4nGT0Labs, wGoctadXGforestS6c4nGT0Nums, 2048),
    (wGoctadXGforestS6c4nGT1Labs, wGoctadXGforestS6c4nGT1Nums, 2048),
    (wGoctadXGforestS6c4nGT2Labs, wGoctadXGforestS6c4nGT2Nums, 2048),
    (wGoctadXGforestS6c4nGT3Labs, wGoctadXGforestS6c4nGT3Nums, 2048)]) : ℚ) / (2 *
    (((tensorWordDenAll wGoctadXGforestS6c4nH : ℚ) * 32) / 2 ^ 12)) =
    wGoctadXGforestS6c4nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms
        [(wGoctadXGforestS6c4nGT0Labs, wGoctadXGforestS6c4nGT0Nums, 2048),
        (wGoctadXGforestS6c4nGT1Labs, wGoctadXGforestS6c4nGT1Nums, 2048),
        (wGoctadXGforestS6c4nGT2Labs, wGoctadXGforestS6c4nGT2Nums, 2048),
        (wGoctadXGforestS6c4nGT3Labs, wGoctadXGforestS6c4nGT3Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 1: equal to the odd self part of the group. -/
theorem wGoctadXGforestS6c4n_og1 : (oddSumF 64 false wGoctadXGforestS6c4nHX0
    (OctadDense.octChunkTerms [(wGoctadXGforestS6c4nGT4Labs, wGoctadXGforestS6c4nGT4Nums, 2048),
    (wGoctadXGforestS6c4nGT5Labs, wGoctadXGforestS6c4nGT5Nums, 2048),
    (wGoctadXGforestS6c4nGT6Labs, wGoctadXGforestS6c4nGT6Nums, 2048),
    (wGoctadXGforestS6c4nGT7Labs, wGoctadXGforestS6c4nGT7Nums, 2048)]) : ℚ) / (2 *
    (((tensorWordDenAll wGoctadXGforestS6c4nH : ℚ) * 32) / 2 ^ 12)) =
    wGoctadXGforestS6c4nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms
        [(wGoctadXGforestS6c4nGT4Labs, wGoctadXGforestS6c4nGT4Nums, 2048),
        (wGoctadXGforestS6c4nGT5Labs, wGoctadXGforestS6c4nGT5Nums, 2048),
        (wGoctadXGforestS6c4nGT6Labs, wGoctadXGforestS6c4nGT6Nums, 2048),
        (wGoctadXGforestS6c4nGT7Labs, wGoctadXGforestS6c4nGT7Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 2: equal to the odd self part of the group. -/
theorem wGoctadXGforestS6c4n_og2 : (oddSumF 64 false wGoctadXGforestS6c4nHX0
    (OctadDense.octChunkTerms [(wGoctadXGforestS6c4nGT8Labs, wGoctadXGforestS6c4nGT8Nums, 2048),
    (wGoctadXGforestS6c4nGT9Labs, wGoctadXGforestS6c4nGT9Nums, 2048),
    (wGoctadXGforestS6c4nGT10Labs, wGoctadXGforestS6c4nGT10Nums, 2048),
    (wGoctadXGforestS6c4nGT11Labs, wGoctadXGforestS6c4nGT11Nums, 2048)]) : ℚ) / (2 *
    (((tensorWordDenAll wGoctadXGforestS6c4nH : ℚ) * 32) / 2 ^ 12)) =
    wGoctadXGforestS6c4nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms
        [(wGoctadXGforestS6c4nGT8Labs, wGoctadXGforestS6c4nGT8Nums, 2048),
        (wGoctadXGforestS6c4nGT9Labs, wGoctadXGforestS6c4nGT9Nums, 2048),
        (wGoctadXGforestS6c4nGT10Labs, wGoctadXGforestS6c4nGT10Nums, 2048),
        (wGoctadXGforestS6c4nGT11Labs, wGoctadXGforestS6c4nGT11Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 3: equal to the odd self part of the group. -/
theorem wGoctadXGforestS6c4n_og3 : (oddSumF 64 false wGoctadXGforestS6c4nHX0
    (OctadDense.octChunkTerms [(wGoctadXGforestS6c4nGT12Labs, wGoctadXGforestS6c4nGT12Nums, 2048),
    (wGoctadXGforestS6c4nGT13Labs, wGoctadXGforestS6c4nGT13Nums, 2048),
    (wGoctadXGforestS6c4nGT14Labs, wGoctadXGforestS6c4nGT14Nums, 2048),
    (wGoctadXGforestS6c4nGT15Labs, wGoctadXGforestS6c4nGT15Nums, 2048)]) : ℚ) / (2 *
    (((tensorWordDenAll wGoctadXGforestS6c4nH : ℚ) * 32) / 2 ^ 12)) =
    wGoctadXGforestS6c4nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms
        [(wGoctadXGforestS6c4nGT12Labs, wGoctadXGforestS6c4nGT12Nums, 2048),
        (wGoctadXGforestS6c4nGT13Labs, wGoctadXGforestS6c4nGT13Nums, 2048),
        (wGoctadXGforestS6c4nGT14Labs, wGoctadXGforestS6c4nGT14Nums, 2048),
        (wGoctadXGforestS6c4nGT15Labs, wGoctadXGforestS6c4nGT15Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 4: equal to the odd self part of the group. -/
theorem wGoctadXGforestS6c4n_og4 : (oddSumF 64 false wGoctadXGforestS6c4nHX0
    (OctadDense.octChunkTerms [(wGoctadXGforestS6c4nGT16Labs, wGoctadXGforestS6c4nGT16Nums, 2048),
    (wGoctadXGforestS6c4nGT17Labs, wGoctadXGforestS6c4nGT17Nums, 2048),
    (wGoctadXGforestS6c4nGT18Labs, wGoctadXGforestS6c4nGT18Nums, 2048),
    (wGoctadXGforestS6c4nGT19Labs, wGoctadXGforestS6c4nGT19Nums, 2048)]) : ℚ) / (2 *
    (((tensorWordDenAll wGoctadXGforestS6c4nH : ℚ) * 32) / 2 ^ 12)) =
    wGoctadXGforestS6c4nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms
        [(wGoctadXGforestS6c4nGT16Labs, wGoctadXGforestS6c4nGT16Nums, 2048),
        (wGoctadXGforestS6c4nGT17Labs, wGoctadXGforestS6c4nGT17Nums, 2048),
        (wGoctadXGforestS6c4nGT18Labs, wGoctadXGforestS6c4nGT18Nums, 2048),
        (wGoctadXGforestS6c4nGT19Labs, wGoctadXGforestS6c4nGT19Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 5: equal to the odd self part of the group. -/
theorem wGoctadXGforestS6c4n_og5 : (oddSumF 64 false wGoctadXGforestS6c4nHX0
    (OctadDense.octChunkTerms [(wGoctadXGforestS6c4nGT20Labs, wGoctadXGforestS6c4nGT20Nums, 2048),
    (wGoctadXGforestS6c4nGT21Labs, wGoctadXGforestS6c4nGT21Nums, 2048),
    (wGoctadXGforestS6c4nGT22Labs, wGoctadXGforestS6c4nGT22Nums, 1026)]) : ℚ) / (2 *
    (((tensorWordDenAll wGoctadXGforestS6c4nH : ℚ) * 32) / 2 ^ 12)) =
    wGoctadXGforestS6c4nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms
        [(wGoctadXGforestS6c4nGT20Labs, wGoctadXGforestS6c4nGT20Nums, 2048),
        (wGoctadXGforestS6c4nGT21Labs, wGoctadXGforestS6c4nGT21Nums, 2048),
        (wGoctadXGforestS6c4nGT22Labs, wGoctadXGforestS6c4nGT22Nums, 1026)])) : ℚ) := by
  decide +kernel

/-- The odd short part equals the odd self part of the target (group checks, no predicted values).
-/
theorem wGoctadXGforestS6c4n_ha : (oddWZ 64 false wGoctadXGforestS6c4nHX0 wGoctadXGforestS6c4nW :
    ℚ) / (2 * (((tensorWordDenAll wGoctadXGforestS6c4nH : ℚ) * 32) / 2 ^ 12)) =
    wGoctadXGforestS6c4nW.sden * (selfOddP wGoctadXGforestS6c4nW : ℚ) :=
  oddPart_of_groups 64 false wGoctadXGforestS6c4nHX0 wGoctadXGforestS6c4nW _
      wGoctadXGforestS6c4n_WshG wGoctadXGforestS6c4n_sd (((tensorWordDenAll wGoctadXGforestS6c4nH
      : ℚ) * 32) / 2 ^ 12) (by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [wGoctadXGforestS6c4n_og0, wGoctadXGforestS6c4n_og1, wGoctadXGforestS6c4n_og2,
        wGoctadXGforestS6c4n_og3, wGoctadXGforestS6c4n_og4, wGoctadXGforestS6c4n_og5])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
