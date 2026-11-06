/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR82nTChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR82nTTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (odd short terms) of the identification Root8[2]- <-> Tenth[38]+ (record
r8f:R82-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target short block as packed chunks, in groups. -/
theorem wR8fR82nT_WshG : wR8fR82nTW.sh = ShortData.ofList [OctadDense.octChunkTerms
    [(wR8fR82nTGT0Labs, wR8fR82nTGT0Nums, 2048), (wR8fR82nTGT1Labs, wR8fR82nTGT1Nums, 2048),
    (wR8fR82nTGT2Labs, wR8fR82nTGT2Nums, 2048), (wR8fR82nTGT3Labs, wR8fR82nTGT3Nums, 2048)],
    OctadDense.octChunkTerms [(wR8fR82nTGT4Labs, wR8fR82nTGT4Nums, 2048), (wR8fR82nTGT5Labs,
    wR8fR82nTGT5Nums, 2048), (wR8fR82nTGT6Labs, wR8fR82nTGT6Nums, 2048), (wR8fR82nTGT7Labs,
    wR8fR82nTGT7Nums, 2048)], OctadDense.octChunkTerms [(wR8fR82nTGT8Labs, wR8fR82nTGT8Nums,
    2048), (wR8fR82nTGT9Labs, wR8fR82nTGT9Nums, 2048), (wR8fR82nTGT10Labs, wR8fR82nTGT10Nums,
    2048), (wR8fR82nTGT11Labs, wR8fR82nTGT11Nums, 2048)], OctadDense.octChunkTerms
    [(wR8fR82nTGT12Labs, wR8fR82nTGT12Nums, 2048), (wR8fR82nTGT13Labs, wR8fR82nTGT13Nums, 2048),
    (wR8fR82nTGT14Labs, wR8fR82nTGT14Nums, 2048), (wR8fR82nTGT15Labs, wR8fR82nTGT15Nums, 2048)],
    OctadDense.octChunkTerms [(wR8fR82nTGT16Labs, wR8fR82nTGT16Nums, 2048), (wR8fR82nTGT17Labs,
    wR8fR82nTGT17Nums, 2048), (wR8fR82nTGT18Labs, wR8fR82nTGT18Nums, 2048), (wR8fR82nTGT19Labs,
    wR8fR82nTGT19Nums, 2048)], OctadDense.octChunkTerms [(wR8fR82nTGT20Labs, wR8fR82nTGT20Nums,
    2048), (wR8fR82nTGT21Labs, wR8fR82nTGT21Nums, 2048), (wR8fR82nTGT22Labs, wR8fR82nTGT22Nums,
    1026)]].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, OctadDense.octChunkTerms,
    List.append_assoc]
  rfl

set_option maxRecDepth 100000 in
/-- The odd labels of the target are distinct. -/
theorem wR8fR82nT_sd : labDistinct wR8fR82nTW.sh.odd 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 0: equal to the odd self part of the group. -/
theorem wR8fR82nT_og0 : (oddSumF 64 false wR8fR82nTHX0 (OctadDense.octChunkTerms
    [(wR8fR82nTGT0Labs, wR8fR82nTGT0Nums, 2048), (wR8fR82nTGT1Labs, wR8fR82nTGT1Nums, 2048),
    (wR8fR82nTGT2Labs, wR8fR82nTGT2Nums, 2048), (wR8fR82nTGT3Labs, wR8fR82nTGT3Nums, 2048)]) : ℚ)
    / (2 * (((tensorWordDenAll wR8fR82nTH : ℚ) * 32) / 2 ^ 12)) =
    wR8fR82nTW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wR8fR82nTGT0Labs,
        wR8fR82nTGT0Nums, 2048), (wR8fR82nTGT1Labs, wR8fR82nTGT1Nums, 2048), (wR8fR82nTGT2Labs,
        wR8fR82nTGT2Nums, 2048), (wR8fR82nTGT3Labs, wR8fR82nTGT3Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 1: equal to the odd self part of the group. -/
theorem wR8fR82nT_og1 : (oddSumF 64 false wR8fR82nTHX0 (OctadDense.octChunkTerms
    [(wR8fR82nTGT4Labs, wR8fR82nTGT4Nums, 2048), (wR8fR82nTGT5Labs, wR8fR82nTGT5Nums, 2048),
    (wR8fR82nTGT6Labs, wR8fR82nTGT6Nums, 2048), (wR8fR82nTGT7Labs, wR8fR82nTGT7Nums, 2048)]) : ℚ)
    / (2 * (((tensorWordDenAll wR8fR82nTH : ℚ) * 32) / 2 ^ 12)) =
    wR8fR82nTW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wR8fR82nTGT4Labs,
        wR8fR82nTGT4Nums, 2048), (wR8fR82nTGT5Labs, wR8fR82nTGT5Nums, 2048), (wR8fR82nTGT6Labs,
        wR8fR82nTGT6Nums, 2048), (wR8fR82nTGT7Labs, wR8fR82nTGT7Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 2: equal to the odd self part of the group. -/
theorem wR8fR82nT_og2 : (oddSumF 64 false wR8fR82nTHX0 (OctadDense.octChunkTerms
    [(wR8fR82nTGT8Labs, wR8fR82nTGT8Nums, 2048), (wR8fR82nTGT9Labs, wR8fR82nTGT9Nums, 2048),
    (wR8fR82nTGT10Labs, wR8fR82nTGT10Nums, 2048), (wR8fR82nTGT11Labs, wR8fR82nTGT11Nums, 2048)]) :
    ℚ) / (2 * (((tensorWordDenAll wR8fR82nTH : ℚ) * 32) / 2 ^ 12)) =
    wR8fR82nTW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wR8fR82nTGT8Labs,
        wR8fR82nTGT8Nums, 2048), (wR8fR82nTGT9Labs, wR8fR82nTGT9Nums, 2048), (wR8fR82nTGT10Labs,
        wR8fR82nTGT10Nums, 2048), (wR8fR82nTGT11Labs, wR8fR82nTGT11Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 3: equal to the odd self part of the group. -/
theorem wR8fR82nT_og3 : (oddSumF 64 false wR8fR82nTHX0 (OctadDense.octChunkTerms
    [(wR8fR82nTGT12Labs, wR8fR82nTGT12Nums, 2048), (wR8fR82nTGT13Labs, wR8fR82nTGT13Nums, 2048),
    (wR8fR82nTGT14Labs, wR8fR82nTGT14Nums, 2048), (wR8fR82nTGT15Labs, wR8fR82nTGT15Nums, 2048)]) :
    ℚ) / (2 * (((tensorWordDenAll wR8fR82nTH : ℚ) * 32) / 2 ^ 12)) =
    wR8fR82nTW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wR8fR82nTGT12Labs,
        wR8fR82nTGT12Nums, 2048), (wR8fR82nTGT13Labs, wR8fR82nTGT13Nums, 2048),
        (wR8fR82nTGT14Labs, wR8fR82nTGT14Nums, 2048), (wR8fR82nTGT15Labs, wR8fR82nTGT15Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 4: equal to the odd self part of the group. -/
theorem wR8fR82nT_og4 : (oddSumF 64 false wR8fR82nTHX0 (OctadDense.octChunkTerms
    [(wR8fR82nTGT16Labs, wR8fR82nTGT16Nums, 2048), (wR8fR82nTGT17Labs, wR8fR82nTGT17Nums, 2048),
    (wR8fR82nTGT18Labs, wR8fR82nTGT18Nums, 2048), (wR8fR82nTGT19Labs, wR8fR82nTGT19Nums, 2048)]) :
    ℚ) / (2 * (((tensorWordDenAll wR8fR82nTH : ℚ) * 32) / 2 ^ 12)) =
    wR8fR82nTW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wR8fR82nTGT16Labs,
        wR8fR82nTGT16Nums, 2048), (wR8fR82nTGT17Labs, wR8fR82nTGT17Nums, 2048),
        (wR8fR82nTGT18Labs, wR8fR82nTGT18Nums, 2048), (wR8fR82nTGT19Labs, wR8fR82nTGT19Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 5: equal to the odd self part of the group. -/
theorem wR8fR82nT_og5 : (oddSumF 64 false wR8fR82nTHX0 (OctadDense.octChunkTerms
    [(wR8fR82nTGT20Labs, wR8fR82nTGT20Nums, 2048), (wR8fR82nTGT21Labs, wR8fR82nTGT21Nums, 2048),
    (wR8fR82nTGT22Labs, wR8fR82nTGT22Nums, 1026)]) : ℚ) / (2 * (((tensorWordDenAll wR8fR82nTH : ℚ)
    * 32) / 2 ^ 12)) =
    wR8fR82nTW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wR8fR82nTGT20Labs,
        wR8fR82nTGT20Nums, 2048), (wR8fR82nTGT21Labs, wR8fR82nTGT21Nums, 2048),
        (wR8fR82nTGT22Labs, wR8fR82nTGT22Nums, 1026)])) : ℚ) := by
  decide +kernel

/-- The odd short part equals the odd self part of the target (group checks, no predicted values).
-/
theorem wR8fR82nT_ha : (oddWZ 64 false wR8fR82nTHX0 wR8fR82nTW : ℚ) / (2 * (((tensorWordDenAll
    wR8fR82nTH : ℚ) * 32) / 2 ^ 12)) =
    wR8fR82nTW.sden * (selfOddP wR8fR82nTW : ℚ) :=
  oddPart_of_groups 64 false wR8fR82nTHX0 wR8fR82nTW _ wR8fR82nT_WshG wR8fR82nT_sd
      (((tensorWordDenAll wR8fR82nTH : ℚ) * 32) / 2 ^ 12) (by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [wR8fR82nT_og0, wR8fR82nT_og1, wR8fR82nT_og2, wR8fR82nT_og3, wR8fR82nT_og4,
        wR8fR82nT_og5])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
