/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c8nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c8nTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (odd short terms) of the identification Eighth[13]+ <-> Seventh[14]- (record
gforest:S7c8-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target short block as packed chunks, in groups. -/
theorem wGforestS7c8n_WshG : wGforestS7c8nW.sh = ShortData.ofList [OctadDense.octChunkTerms
    [(wGforestS7c8nGT0Labs, wGforestS7c8nGT0Nums, 2048), (wGforestS7c8nGT1Labs,
    wGforestS7c8nGT1Nums, 2048), (wGforestS7c8nGT2Labs, wGforestS7c8nGT2Nums, 2048),
    (wGforestS7c8nGT3Labs, wGforestS7c8nGT3Nums, 2048)], OctadDense.octChunkTerms
    [(wGforestS7c8nGT4Labs, wGforestS7c8nGT4Nums, 2048), (wGforestS7c8nGT5Labs,
    wGforestS7c8nGT5Nums, 2048), (wGforestS7c8nGT6Labs, wGforestS7c8nGT6Nums, 2048),
    (wGforestS7c8nGT7Labs, wGforestS7c8nGT7Nums, 2048)], OctadDense.octChunkTerms
    [(wGforestS7c8nGT8Labs, wGforestS7c8nGT8Nums, 2048), (wGforestS7c8nGT9Labs,
    wGforestS7c8nGT9Nums, 2048), (wGforestS7c8nGT10Labs, wGforestS7c8nGT10Nums, 2048),
    (wGforestS7c8nGT11Labs, wGforestS7c8nGT11Nums, 2048)], OctadDense.octChunkTerms
    [(wGforestS7c8nGT12Labs, wGforestS7c8nGT12Nums, 2048), (wGforestS7c8nGT13Labs,
    wGforestS7c8nGT13Nums, 2048), (wGforestS7c8nGT14Labs, wGforestS7c8nGT14Nums, 2048),
    (wGforestS7c8nGT15Labs, wGforestS7c8nGT15Nums, 2048)], OctadDense.octChunkTerms
    [(wGforestS7c8nGT16Labs, wGforestS7c8nGT16Nums, 2048), (wGforestS7c8nGT17Labs,
    wGforestS7c8nGT17Nums, 2048), (wGforestS7c8nGT18Labs, wGforestS7c8nGT18Nums, 2048),
    (wGforestS7c8nGT19Labs, wGforestS7c8nGT19Nums, 2048)], OctadDense.octChunkTerms
    [(wGforestS7c8nGT20Labs, wGforestS7c8nGT20Nums, 2048), (wGforestS7c8nGT21Labs,
    wGforestS7c8nGT21Nums, 668)]].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, OctadDense.octChunkTerms,
    List.append_assoc]
  rfl

set_option maxRecDepth 100000 in
/-- The odd labels of the target are distinct. -/
theorem wGforestS7c8n_sd : labDistinct wGforestS7c8nW.sh.odd 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 0: equal to the odd self part of the group. -/
theorem wGforestS7c8n_og0 : (oddSumF 72 false wGforestS7c8nHX0 (OctadDense.octChunkTerms
    [(wGforestS7c8nGT0Labs, wGforestS7c8nGT0Nums, 2048), (wGforestS7c8nGT1Labs,
    wGforestS7c8nGT1Nums, 2048), (wGforestS7c8nGT2Labs, wGforestS7c8nGT2Nums, 2048),
    (wGforestS7c8nGT3Labs, wGforestS7c8nGT3Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGforestS7c8nH : ℚ) * srcSeventhD0) / 2 ^ 20)) =
    wGforestS7c8nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGforestS7c8nGT0Labs,
        wGforestS7c8nGT0Nums, 2048), (wGforestS7c8nGT1Labs, wGforestS7c8nGT1Nums, 2048),
        (wGforestS7c8nGT2Labs, wGforestS7c8nGT2Nums, 2048), (wGforestS7c8nGT3Labs,
        wGforestS7c8nGT3Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 1: equal to the odd self part of the group. -/
theorem wGforestS7c8n_og1 : (oddSumF 72 false wGforestS7c8nHX0 (OctadDense.octChunkTerms
    [(wGforestS7c8nGT4Labs, wGforestS7c8nGT4Nums, 2048), (wGforestS7c8nGT5Labs,
    wGforestS7c8nGT5Nums, 2048), (wGforestS7c8nGT6Labs, wGforestS7c8nGT6Nums, 2048),
    (wGforestS7c8nGT7Labs, wGforestS7c8nGT7Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGforestS7c8nH : ℚ) * srcSeventhD0) / 2 ^ 20)) =
    wGforestS7c8nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGforestS7c8nGT4Labs,
        wGforestS7c8nGT4Nums, 2048), (wGforestS7c8nGT5Labs, wGforestS7c8nGT5Nums, 2048),
        (wGforestS7c8nGT6Labs, wGforestS7c8nGT6Nums, 2048), (wGforestS7c8nGT7Labs,
        wGforestS7c8nGT7Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 2: equal to the odd self part of the group. -/
theorem wGforestS7c8n_og2 : (oddSumF 72 false wGforestS7c8nHX0 (OctadDense.octChunkTerms
    [(wGforestS7c8nGT8Labs, wGforestS7c8nGT8Nums, 2048), (wGforestS7c8nGT9Labs,
    wGforestS7c8nGT9Nums, 2048), (wGforestS7c8nGT10Labs, wGforestS7c8nGT10Nums, 2048),
    (wGforestS7c8nGT11Labs, wGforestS7c8nGT11Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGforestS7c8nH : ℚ) * srcSeventhD0) / 2 ^ 20)) =
    wGforestS7c8nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGforestS7c8nGT8Labs,
        wGforestS7c8nGT8Nums, 2048), (wGforestS7c8nGT9Labs, wGforestS7c8nGT9Nums, 2048),
        (wGforestS7c8nGT10Labs, wGforestS7c8nGT10Nums, 2048), (wGforestS7c8nGT11Labs,
        wGforestS7c8nGT11Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 3: equal to the odd self part of the group. -/
theorem wGforestS7c8n_og3 : (oddSumF 72 false wGforestS7c8nHX0 (OctadDense.octChunkTerms
    [(wGforestS7c8nGT12Labs, wGforestS7c8nGT12Nums, 2048), (wGforestS7c8nGT13Labs,
    wGforestS7c8nGT13Nums, 2048), (wGforestS7c8nGT14Labs, wGforestS7c8nGT14Nums, 2048),
    (wGforestS7c8nGT15Labs, wGforestS7c8nGT15Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGforestS7c8nH : ℚ) * srcSeventhD0) / 2 ^ 20)) =
    wGforestS7c8nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGforestS7c8nGT12Labs,
        wGforestS7c8nGT12Nums, 2048), (wGforestS7c8nGT13Labs, wGforestS7c8nGT13Nums, 2048),
        (wGforestS7c8nGT14Labs, wGforestS7c8nGT14Nums, 2048), (wGforestS7c8nGT15Labs,
        wGforestS7c8nGT15Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 4: equal to the odd self part of the group. -/
theorem wGforestS7c8n_og4 : (oddSumF 72 false wGforestS7c8nHX0 (OctadDense.octChunkTerms
    [(wGforestS7c8nGT16Labs, wGforestS7c8nGT16Nums, 2048), (wGforestS7c8nGT17Labs,
    wGforestS7c8nGT17Nums, 2048), (wGforestS7c8nGT18Labs, wGforestS7c8nGT18Nums, 2048),
    (wGforestS7c8nGT19Labs, wGforestS7c8nGT19Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll
    wGforestS7c8nH : ℚ) * srcSeventhD0) / 2 ^ 20)) =
    wGforestS7c8nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGforestS7c8nGT16Labs,
        wGforestS7c8nGT16Nums, 2048), (wGforestS7c8nGT17Labs, wGforestS7c8nGT17Nums, 2048),
        (wGforestS7c8nGT18Labs, wGforestS7c8nGT18Nums, 2048), (wGforestS7c8nGT19Labs,
        wGforestS7c8nGT19Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 5: equal to the odd self part of the group. -/
theorem wGforestS7c8n_og5 : (oddSumF 72 false wGforestS7c8nHX0 (OctadDense.octChunkTerms
    [(wGforestS7c8nGT20Labs, wGforestS7c8nGT20Nums, 2048), (wGforestS7c8nGT21Labs,
    wGforestS7c8nGT21Nums, 668)]) : ℚ) / (2 * (((tensorWordDenAll wGforestS7c8nH : ℚ) *
    srcSeventhD0) / 2 ^ 20)) =
    wGforestS7c8nW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGforestS7c8nGT20Labs,
        wGforestS7c8nGT20Nums, 2048), (wGforestS7c8nGT21Labs, wGforestS7c8nGT21Nums, 668)])) : ℚ)
        := by
  decide +kernel

/-- The odd short part equals the odd self part of the target (group checks, no predicted values).
-/
theorem wGforestS7c8n_ha : (oddWZ 72 false wGforestS7c8nHX0 wGforestS7c8nW : ℚ) / (2 *
    (((tensorWordDenAll wGforestS7c8nH : ℚ) * srcSeventhD0) / 2 ^ 20)) =
    wGforestS7c8nW.sden * (selfOddP wGforestS7c8nW : ℚ) :=
  oddPart_of_groups 72 false wGforestS7c8nHX0 wGforestS7c8nW _ wGforestS7c8n_WshG wGforestS7c8n_sd
      (((tensorWordDenAll wGforestS7c8nH : ℚ) * srcSeventhD0) / 2 ^ 20) (by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [wGforestS7c8n_og0, wGforestS7c8n_og1, wGforestS7c8n_og2, wGforestS7c8n_og3,
        wGforestS7c8n_og4, wGforestS7c8n_og5])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
