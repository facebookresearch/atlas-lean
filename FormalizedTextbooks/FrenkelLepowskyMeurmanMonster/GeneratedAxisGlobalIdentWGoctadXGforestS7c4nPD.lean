/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS7c4nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS7c4nTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (odd short terms) of the identification Seventh[9]- <-> Tenth[1]+ (record
gforest:S7c4-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target short block as packed chunks, in groups. -/
theorem wGoctadXGforestS7c4n_WshG : wGoctadXGforestS7c4nW.sh = ShortData.ofList
    [OctadDense.octChunkTerms [(wGoctadXGforestS7c4nGT0Labs, wGoctadXGforestS7c4nGT0Nums, 2048),
    (wGoctadXGforestS7c4nGT1Labs, wGoctadXGforestS7c4nGT1Nums, 2048),
    (wGoctadXGforestS7c4nGT2Labs, wGoctadXGforestS7c4nGT2Nums, 2048),
    (wGoctadXGforestS7c4nGT3Labs, wGoctadXGforestS7c4nGT3Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadXGforestS7c4nGT4Labs, wGoctadXGforestS7c4nGT4Nums, 2048),
    (wGoctadXGforestS7c4nGT5Labs, wGoctadXGforestS7c4nGT5Nums, 2048),
    (wGoctadXGforestS7c4nGT6Labs, wGoctadXGforestS7c4nGT6Nums, 2048),
    (wGoctadXGforestS7c4nGT7Labs, wGoctadXGforestS7c4nGT7Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadXGforestS7c4nGT8Labs, wGoctadXGforestS7c4nGT8Nums, 2048),
    (wGoctadXGforestS7c4nGT9Labs, wGoctadXGforestS7c4nGT9Nums, 2048),
    (wGoctadXGforestS7c4nGT10Labs, wGoctadXGforestS7c4nGT10Nums, 2048),
    (wGoctadXGforestS7c4nGT11Labs, wGoctadXGforestS7c4nGT11Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadXGforestS7c4nGT12Labs, wGoctadXGforestS7c4nGT12Nums, 2048),
    (wGoctadXGforestS7c4nGT13Labs, wGoctadXGforestS7c4nGT13Nums, 2048),
    (wGoctadXGforestS7c4nGT14Labs, wGoctadXGforestS7c4nGT14Nums, 2048),
    (wGoctadXGforestS7c4nGT15Labs, wGoctadXGforestS7c4nGT15Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadXGforestS7c4nGT16Labs, wGoctadXGforestS7c4nGT16Nums, 2048),
    (wGoctadXGforestS7c4nGT17Labs, wGoctadXGforestS7c4nGT17Nums, 2048),
    (wGoctadXGforestS7c4nGT18Labs, wGoctadXGforestS7c4nGT18Nums, 2048),
    (wGoctadXGforestS7c4nGT19Labs, wGoctadXGforestS7c4nGT19Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadXGforestS7c4nGT20Labs, wGoctadXGforestS7c4nGT20Nums, 2048),
    (wGoctadXGforestS7c4nGT21Labs, wGoctadXGforestS7c4nGT21Nums, 2048),
    (wGoctadXGforestS7c4nGT22Labs, wGoctadXGforestS7c4nGT22Nums, 1026)]].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, OctadDense.octChunkTerms,
    List.append_assoc]
  rfl

set_option maxRecDepth 100000 in
/-- The odd labels of the target are distinct. -/
theorem wGoctadXGforestS7c4n_sd : labDistinct wGoctadXGforestS7c4nW.sh.odd 0 = true := by
    decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 0: equal to the odd self part of the group. -/
theorem wGoctadXGforestS7c4n_og0 : (oddSumF 64 false wGoctadXGforestS7c4nHX0
    (OctadDense.octChunkTerms [(wGoctadXGforestS7c4nGT0Labs, wGoctadXGforestS7c4nGT0Nums, 2048),
    (wGoctadXGforestS7c4nGT1Labs, wGoctadXGforestS7c4nGT1Nums, 2048),
    (wGoctadXGforestS7c4nGT2Labs, wGoctadXGforestS7c4nGT2Nums, 2048),
    (wGoctadXGforestS7c4nGT3Labs, wGoctadXGforestS7c4nGT3Nums, 2048)]) : ℚ) / (2 *
    (((tensorWordDenAll wGoctadXGforestS7c4nH : ℚ) * srcSeventhD0) / 2 ^ 20)) =
    wGoctadXGforestS7c4nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms
        [(wGoctadXGforestS7c4nGT0Labs, wGoctadXGforestS7c4nGT0Nums, 2048),
        (wGoctadXGforestS7c4nGT1Labs, wGoctadXGforestS7c4nGT1Nums, 2048),
        (wGoctadXGforestS7c4nGT2Labs, wGoctadXGforestS7c4nGT2Nums, 2048),
        (wGoctadXGforestS7c4nGT3Labs, wGoctadXGforestS7c4nGT3Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 1: equal to the odd self part of the group. -/
theorem wGoctadXGforestS7c4n_og1 : (oddSumF 64 false wGoctadXGforestS7c4nHX0
    (OctadDense.octChunkTerms [(wGoctadXGforestS7c4nGT4Labs, wGoctadXGforestS7c4nGT4Nums, 2048),
    (wGoctadXGforestS7c4nGT5Labs, wGoctadXGforestS7c4nGT5Nums, 2048),
    (wGoctadXGforestS7c4nGT6Labs, wGoctadXGforestS7c4nGT6Nums, 2048),
    (wGoctadXGforestS7c4nGT7Labs, wGoctadXGforestS7c4nGT7Nums, 2048)]) : ℚ) / (2 *
    (((tensorWordDenAll wGoctadXGforestS7c4nH : ℚ) * srcSeventhD0) / 2 ^ 20)) =
    wGoctadXGforestS7c4nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms
        [(wGoctadXGforestS7c4nGT4Labs, wGoctadXGforestS7c4nGT4Nums, 2048),
        (wGoctadXGforestS7c4nGT5Labs, wGoctadXGforestS7c4nGT5Nums, 2048),
        (wGoctadXGforestS7c4nGT6Labs, wGoctadXGforestS7c4nGT6Nums, 2048),
        (wGoctadXGforestS7c4nGT7Labs, wGoctadXGforestS7c4nGT7Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 2: equal to the odd self part of the group. -/
theorem wGoctadXGforestS7c4n_og2 : (oddSumF 64 false wGoctadXGforestS7c4nHX0
    (OctadDense.octChunkTerms [(wGoctadXGforestS7c4nGT8Labs, wGoctadXGforestS7c4nGT8Nums, 2048),
    (wGoctadXGforestS7c4nGT9Labs, wGoctadXGforestS7c4nGT9Nums, 2048),
    (wGoctadXGforestS7c4nGT10Labs, wGoctadXGforestS7c4nGT10Nums, 2048),
    (wGoctadXGforestS7c4nGT11Labs, wGoctadXGforestS7c4nGT11Nums, 2048)]) : ℚ) / (2 *
    (((tensorWordDenAll wGoctadXGforestS7c4nH : ℚ) * srcSeventhD0) / 2 ^ 20)) =
    wGoctadXGforestS7c4nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms
        [(wGoctadXGforestS7c4nGT8Labs, wGoctadXGforestS7c4nGT8Nums, 2048),
        (wGoctadXGforestS7c4nGT9Labs, wGoctadXGforestS7c4nGT9Nums, 2048),
        (wGoctadXGforestS7c4nGT10Labs, wGoctadXGforestS7c4nGT10Nums, 2048),
        (wGoctadXGforestS7c4nGT11Labs, wGoctadXGforestS7c4nGT11Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 3: equal to the odd self part of the group. -/
theorem wGoctadXGforestS7c4n_og3 : (oddSumF 64 false wGoctadXGforestS7c4nHX0
    (OctadDense.octChunkTerms [(wGoctadXGforestS7c4nGT12Labs, wGoctadXGforestS7c4nGT12Nums, 2048),
    (wGoctadXGforestS7c4nGT13Labs, wGoctadXGforestS7c4nGT13Nums, 2048),
    (wGoctadXGforestS7c4nGT14Labs, wGoctadXGforestS7c4nGT14Nums, 2048),
    (wGoctadXGforestS7c4nGT15Labs, wGoctadXGforestS7c4nGT15Nums, 2048)]) : ℚ) / (2 *
    (((tensorWordDenAll wGoctadXGforestS7c4nH : ℚ) * srcSeventhD0) / 2 ^ 20)) =
    wGoctadXGforestS7c4nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms
        [(wGoctadXGforestS7c4nGT12Labs, wGoctadXGforestS7c4nGT12Nums, 2048),
        (wGoctadXGforestS7c4nGT13Labs, wGoctadXGforestS7c4nGT13Nums, 2048),
        (wGoctadXGforestS7c4nGT14Labs, wGoctadXGforestS7c4nGT14Nums, 2048),
        (wGoctadXGforestS7c4nGT15Labs, wGoctadXGforestS7c4nGT15Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 4: equal to the odd self part of the group. -/
theorem wGoctadXGforestS7c4n_og4 : (oddSumF 64 false wGoctadXGforestS7c4nHX0
    (OctadDense.octChunkTerms [(wGoctadXGforestS7c4nGT16Labs, wGoctadXGforestS7c4nGT16Nums, 2048),
    (wGoctadXGforestS7c4nGT17Labs, wGoctadXGforestS7c4nGT17Nums, 2048),
    (wGoctadXGforestS7c4nGT18Labs, wGoctadXGforestS7c4nGT18Nums, 2048),
    (wGoctadXGforestS7c4nGT19Labs, wGoctadXGforestS7c4nGT19Nums, 2048)]) : ℚ) / (2 *
    (((tensorWordDenAll wGoctadXGforestS7c4nH : ℚ) * srcSeventhD0) / 2 ^ 20)) =
    wGoctadXGforestS7c4nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms
        [(wGoctadXGforestS7c4nGT16Labs, wGoctadXGforestS7c4nGT16Nums, 2048),
        (wGoctadXGforestS7c4nGT17Labs, wGoctadXGforestS7c4nGT17Nums, 2048),
        (wGoctadXGforestS7c4nGT18Labs, wGoctadXGforestS7c4nGT18Nums, 2048),
        (wGoctadXGforestS7c4nGT19Labs, wGoctadXGforestS7c4nGT19Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 5: equal to the odd self part of the group. -/
theorem wGoctadXGforestS7c4n_og5 : (oddSumF 64 false wGoctadXGforestS7c4nHX0
    (OctadDense.octChunkTerms [(wGoctadXGforestS7c4nGT20Labs, wGoctadXGforestS7c4nGT20Nums, 2048),
    (wGoctadXGforestS7c4nGT21Labs, wGoctadXGforestS7c4nGT21Nums, 2048),
    (wGoctadXGforestS7c4nGT22Labs, wGoctadXGforestS7c4nGT22Nums, 1026)]) : ℚ) / (2 *
    (((tensorWordDenAll wGoctadXGforestS7c4nH : ℚ) * srcSeventhD0) / 2 ^ 20)) =
    wGoctadXGforestS7c4nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms
        [(wGoctadXGforestS7c4nGT20Labs, wGoctadXGforestS7c4nGT20Nums, 2048),
        (wGoctadXGforestS7c4nGT21Labs, wGoctadXGforestS7c4nGT21Nums, 2048),
        (wGoctadXGforestS7c4nGT22Labs, wGoctadXGforestS7c4nGT22Nums, 1026)])) : ℚ) := by
  decide +kernel

/-- The odd short part equals the odd self part of the target (group checks, no predicted values).
-/
theorem wGoctadXGforestS7c4n_ha : (oddWZ 64 false wGoctadXGforestS7c4nHX0 wGoctadXGforestS7c4nW :
    ℚ) / (2 * (((tensorWordDenAll wGoctadXGforestS7c4nH : ℚ) * srcSeventhD0) / 2 ^ 20)) =
    wGoctadXGforestS7c4nW.sden * (selfOddP wGoctadXGforestS7c4nW : ℚ) :=
  oddPart_of_groups 64 false wGoctadXGforestS7c4nHX0 wGoctadXGforestS7c4nW _
      wGoctadXGforestS7c4n_WshG wGoctadXGforestS7c4n_sd (((tensorWordDenAll wGoctadXGforestS7c4nH
      : ℚ) * srcSeventhD0) / 2 ^ 20) (by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [wGoctadXGforestS7c4n_og0, wGoctadXGforestS7c4n_og1, wGoctadXGforestS7c4n_og2,
        wGoctadXGforestS7c4n_og3, wGoctadXGforestS7c4n_og4, wGoctadXGforestS7c4n_og5])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
