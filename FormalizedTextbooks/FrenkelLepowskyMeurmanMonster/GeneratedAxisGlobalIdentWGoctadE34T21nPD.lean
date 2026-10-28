/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE34T21nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE34T21nTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (odd short terms) of the identification Eighth[47]- <-> Tenth[26]+ (record
goctad:E34@T21-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target short block as packed chunks, in groups. -/
theorem wGoctadE34T21n_WshG : wGoctadE34T21nW.sh = ShortData.ofList [OctadDense.octChunkTerms
    [(wGoctadE34T21nGT0Labs, wGoctadE34T21nGT0Nums, 2048), (wGoctadE34T21nGT1Labs,
    wGoctadE34T21nGT1Nums, 2048), (wGoctadE34T21nGT2Labs, wGoctadE34T21nGT2Nums, 2048),
    (wGoctadE34T21nGT3Labs, wGoctadE34T21nGT3Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadE34T21nGT4Labs, wGoctadE34T21nGT4Nums, 2048), (wGoctadE34T21nGT5Labs,
    wGoctadE34T21nGT5Nums, 2048), (wGoctadE34T21nGT6Labs, wGoctadE34T21nGT6Nums, 2048),
    (wGoctadE34T21nGT7Labs, wGoctadE34T21nGT7Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadE34T21nGT8Labs, wGoctadE34T21nGT8Nums, 2048), (wGoctadE34T21nGT9Labs,
    wGoctadE34T21nGT9Nums, 2048), (wGoctadE34T21nGT10Labs, wGoctadE34T21nGT10Nums, 2048),
    (wGoctadE34T21nGT11Labs, wGoctadE34T21nGT11Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadE34T21nGT12Labs, wGoctadE34T21nGT12Nums, 2048), (wGoctadE34T21nGT13Labs,
    wGoctadE34T21nGT13Nums, 2048), (wGoctadE34T21nGT14Labs, wGoctadE34T21nGT14Nums, 2048),
    (wGoctadE34T21nGT15Labs, wGoctadE34T21nGT15Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadE34T21nGT16Labs, wGoctadE34T21nGT16Nums, 2048), (wGoctadE34T21nGT17Labs,
    wGoctadE34T21nGT17Nums, 2048), (wGoctadE34T21nGT18Labs, wGoctadE34T21nGT18Nums, 2048),
    (wGoctadE34T21nGT19Labs, wGoctadE34T21nGT19Nums, 2048)], OctadDense.octChunkTerms
    [(wGoctadE34T21nGT20Labs, wGoctadE34T21nGT20Nums, 2048), (wGoctadE34T21nGT21Labs,
    wGoctadE34T21nGT21Nums, 2048), (wGoctadE34T21nGT22Labs, wGoctadE34T21nGT22Nums,
    1026)]].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, OctadDense.octChunkTerms,
    List.append_assoc]
  rfl

set_option maxRecDepth 100000 in
/-- The odd labels of the target are distinct. -/
theorem wGoctadE34T21n_sd : labDistinct wGoctadE34T21nW.sh.odd 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 0: equal to the odd self part of the group. -/
theorem wGoctadE34T21n_og0 : (oddSumF 72 false wGoctadE34T21nHX0 (OctadDense.octChunkTerms
    [(wGoctadE34T21nGT0Labs, wGoctadE34T21nGT0Nums, 2048), (wGoctadE34T21nGT1Labs,
    wGoctadE34T21nGT1Nums, 2048), (wGoctadE34T21nGT2Labs, wGoctadE34T21nGT2Nums, 2048),
    (wGoctadE34T21nGT3Labs, wGoctadE34T21nGT3Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGoctadE34T21nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 33)) =
    wGoctadE34T21nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE34T21nGT0Labs,
        wGoctadE34T21nGT0Nums, 2048), (wGoctadE34T21nGT1Labs, wGoctadE34T21nGT1Nums, 2048),
        (wGoctadE34T21nGT2Labs, wGoctadE34T21nGT2Nums, 2048), (wGoctadE34T21nGT3Labs,
        wGoctadE34T21nGT3Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 1: equal to the odd self part of the group. -/
theorem wGoctadE34T21n_og1 : (oddSumF 72 false wGoctadE34T21nHX0 (OctadDense.octChunkTerms
    [(wGoctadE34T21nGT4Labs, wGoctadE34T21nGT4Nums, 2048), (wGoctadE34T21nGT5Labs,
    wGoctadE34T21nGT5Nums, 2048), (wGoctadE34T21nGT6Labs, wGoctadE34T21nGT6Nums, 2048),
    (wGoctadE34T21nGT7Labs, wGoctadE34T21nGT7Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGoctadE34T21nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 33)) =
    wGoctadE34T21nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE34T21nGT4Labs,
        wGoctadE34T21nGT4Nums, 2048), (wGoctadE34T21nGT5Labs, wGoctadE34T21nGT5Nums, 2048),
        (wGoctadE34T21nGT6Labs, wGoctadE34T21nGT6Nums, 2048), (wGoctadE34T21nGT7Labs,
        wGoctadE34T21nGT7Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 2: equal to the odd self part of the group. -/
theorem wGoctadE34T21n_og2 : (oddSumF 72 false wGoctadE34T21nHX0 (OctadDense.octChunkTerms
    [(wGoctadE34T21nGT8Labs, wGoctadE34T21nGT8Nums, 2048), (wGoctadE34T21nGT9Labs,
    wGoctadE34T21nGT9Nums, 2048), (wGoctadE34T21nGT10Labs, wGoctadE34T21nGT10Nums, 2048),
    (wGoctadE34T21nGT11Labs, wGoctadE34T21nGT11Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGoctadE34T21nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 33)) =
    wGoctadE34T21nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE34T21nGT8Labs,
        wGoctadE34T21nGT8Nums, 2048), (wGoctadE34T21nGT9Labs, wGoctadE34T21nGT9Nums, 2048),
        (wGoctadE34T21nGT10Labs, wGoctadE34T21nGT10Nums, 2048), (wGoctadE34T21nGT11Labs,
        wGoctadE34T21nGT11Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 3: equal to the odd self part of the group. -/
theorem wGoctadE34T21n_og3 : (oddSumF 72 false wGoctadE34T21nHX0 (OctadDense.octChunkTerms
    [(wGoctadE34T21nGT12Labs, wGoctadE34T21nGT12Nums, 2048), (wGoctadE34T21nGT13Labs,
    wGoctadE34T21nGT13Nums, 2048), (wGoctadE34T21nGT14Labs, wGoctadE34T21nGT14Nums, 2048),
    (wGoctadE34T21nGT15Labs, wGoctadE34T21nGT15Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGoctadE34T21nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 33)) =
    wGoctadE34T21nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE34T21nGT12Labs,
        wGoctadE34T21nGT12Nums, 2048), (wGoctadE34T21nGT13Labs, wGoctadE34T21nGT13Nums, 2048),
        (wGoctadE34T21nGT14Labs, wGoctadE34T21nGT14Nums, 2048), (wGoctadE34T21nGT15Labs,
        wGoctadE34T21nGT15Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 4: equal to the odd self part of the group. -/
theorem wGoctadE34T21n_og4 : (oddSumF 72 false wGoctadE34T21nHX0 (OctadDense.octChunkTerms
    [(wGoctadE34T21nGT16Labs, wGoctadE34T21nGT16Nums, 2048), (wGoctadE34T21nGT17Labs,
    wGoctadE34T21nGT17Nums, 2048), (wGoctadE34T21nGT18Labs, wGoctadE34T21nGT18Nums, 2048),
    (wGoctadE34T21nGT19Labs, wGoctadE34T21nGT19Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGoctadE34T21nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2 ^ 33)) =
    wGoctadE34T21nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE34T21nGT16Labs,
        wGoctadE34T21nGT16Nums, 2048), (wGoctadE34T21nGT17Labs, wGoctadE34T21nGT17Nums, 2048),
        (wGoctadE34T21nGT18Labs, wGoctadE34T21nGT18Nums, 2048), (wGoctadE34T21nGT19Labs,
        wGoctadE34T21nGT19Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 5: equal to the odd self part of the group. -/
theorem wGoctadE34T21n_og5 : (oddSumF 72 false wGoctadE34T21nHX0 (OctadDense.octChunkTerms
    [(wGoctadE34T21nGT20Labs, wGoctadE34T21nGT20Nums, 2048), (wGoctadE34T21nGT21Labs,
    wGoctadE34T21nGT21Nums, 2048), (wGoctadE34T21nGT22Labs, wGoctadE34T21nGT22Nums, 1026)]) : ℚ) /
    (2 * (((tensorWordDenAll wGoctadE34T21nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)))
    / 2 ^ 33)) =
    wGoctadE34T21nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGoctadE34T21nGT20Labs,
        wGoctadE34T21nGT20Nums, 2048), (wGoctadE34T21nGT21Labs, wGoctadE34T21nGT21Nums, 2048),
        (wGoctadE34T21nGT22Labs, wGoctadE34T21nGT22Nums, 1026)])) : ℚ) := by
  decide +kernel

/-- The odd short part equals the odd self part of the target (group checks, no predicted values).
-/
theorem wGoctadE34T21n_ha : (oddWZ 72 false wGoctadE34T21nHX0 wGoctadE34T21nW : ℚ) / (2 *
    (((tensorWordDenAll wGoctadE34T21nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) / 2
    ^ 33)) =
    wGoctadE34T21nW.sden * (selfOddP wGoctadE34T21nW : ℚ) :=
  oddPart_of_groups 72 false wGoctadE34T21nHX0 wGoctadE34T21nW _ wGoctadE34T21n_WshG
      wGoctadE34T21n_sd (((tensorWordDenAll wGoctadE34T21nH : ℚ) * (2 * ((tensorWordDenAll
      srcEighthH : ℚ) * 1))) / 2 ^ 33) (by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [wGoctadE34T21n_og0, wGoctadE34T21n_og1, wGoctadE34T21n_og2, wGoctadE34T21n_og3,
        wGoctadE34T21n_og4, wGoctadE34T21n_og5])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
