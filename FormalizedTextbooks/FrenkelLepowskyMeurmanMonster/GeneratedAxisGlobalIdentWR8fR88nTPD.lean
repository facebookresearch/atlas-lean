/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR88nTChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR88nTTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (odd short terms) of the identification Root8[20]- <-> Tenth[69]+ (record
r8f:R88-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target short block as packed chunks, in groups. -/
theorem wR8fR88nT_WshG : wR8fR88nTW.sh = ShortData.ofList [OctadDense.octChunkTerms
    [(wR8fR88nTGT0Labs, wR8fR88nTGT0Nums, 2048), (wR8fR88nTGT1Labs, wR8fR88nTGT1Nums, 2048),
    (wR8fR88nTGT2Labs, wR8fR88nTGT2Nums, 2048), (wR8fR88nTGT3Labs, wR8fR88nTGT3Nums, 2048)],
    OctadDense.octChunkTerms [(wR8fR88nTGT4Labs, wR8fR88nTGT4Nums, 2048), (wR8fR88nTGT5Labs,
    wR8fR88nTGT5Nums, 2048), (wR8fR88nTGT6Labs, wR8fR88nTGT6Nums, 2048), (wR8fR88nTGT7Labs,
    wR8fR88nTGT7Nums, 2048)], OctadDense.octChunkTerms [(wR8fR88nTGT8Labs, wR8fR88nTGT8Nums,
    2048), (wR8fR88nTGT9Labs, wR8fR88nTGT9Nums, 2048), (wR8fR88nTGT10Labs, wR8fR88nTGT10Nums,
    2048), (wR8fR88nTGT11Labs, wR8fR88nTGT11Nums, 2048)], OctadDense.octChunkTerms
    [(wR8fR88nTGT12Labs, wR8fR88nTGT12Nums, 2048), (wR8fR88nTGT13Labs, wR8fR88nTGT13Nums, 2048),
    (wR8fR88nTGT14Labs, wR8fR88nTGT14Nums, 2048), (wR8fR88nTGT15Labs, wR8fR88nTGT15Nums, 2048)],
    OctadDense.octChunkTerms [(wR8fR88nTGT16Labs, wR8fR88nTGT16Nums, 2048), (wR8fR88nTGT17Labs,
    wR8fR88nTGT17Nums, 2048), (wR8fR88nTGT18Labs, wR8fR88nTGT18Nums, 2048), (wR8fR88nTGT19Labs,
    wR8fR88nTGT19Nums, 2048)], OctadDense.octChunkTerms [(wR8fR88nTGT20Labs, wR8fR88nTGT20Nums,
    2048), (wR8fR88nTGT21Labs, wR8fR88nTGT21Nums, 2048), (wR8fR88nTGT22Labs, wR8fR88nTGT22Nums,
    1026)]].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, OctadDense.octChunkTerms,
    List.append_assoc]
  rfl

set_option maxRecDepth 100000 in
/-- The odd labels of the target are distinct. -/
theorem wR8fR88nT_sd : labDistinct wR8fR88nTW.sh.odd 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 0: equal to the odd self part of the group. -/
theorem wR8fR88nT_og0 : (oddSumF 64 false wR8fR88nTHX0 (OctadDense.octChunkTerms
    [(wR8fR88nTGT0Labs, wR8fR88nTGT0Nums, 2048), (wR8fR88nTGT1Labs, wR8fR88nTGT1Nums, 2048),
    (wR8fR88nTGT2Labs, wR8fR88nTGT2Nums, 2048), (wR8fR88nTGT3Labs, wR8fR88nTGT3Nums, 2048)]) : ℚ)
    / (2 * (((tensorWordDenAll wR8fR88nTH : ℚ) * 32) / 2 ^ 16)) =
    wR8fR88nTW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wR8fR88nTGT0Labs,
        wR8fR88nTGT0Nums, 2048), (wR8fR88nTGT1Labs, wR8fR88nTGT1Nums, 2048), (wR8fR88nTGT2Labs,
        wR8fR88nTGT2Nums, 2048), (wR8fR88nTGT3Labs, wR8fR88nTGT3Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 1: equal to the odd self part of the group. -/
theorem wR8fR88nT_og1 : (oddSumF 64 false wR8fR88nTHX0 (OctadDense.octChunkTerms
    [(wR8fR88nTGT4Labs, wR8fR88nTGT4Nums, 2048), (wR8fR88nTGT5Labs, wR8fR88nTGT5Nums, 2048),
    (wR8fR88nTGT6Labs, wR8fR88nTGT6Nums, 2048), (wR8fR88nTGT7Labs, wR8fR88nTGT7Nums, 2048)]) : ℚ)
    / (2 * (((tensorWordDenAll wR8fR88nTH : ℚ) * 32) / 2 ^ 16)) =
    wR8fR88nTW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wR8fR88nTGT4Labs,
        wR8fR88nTGT4Nums, 2048), (wR8fR88nTGT5Labs, wR8fR88nTGT5Nums, 2048), (wR8fR88nTGT6Labs,
        wR8fR88nTGT6Nums, 2048), (wR8fR88nTGT7Labs, wR8fR88nTGT7Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 2: equal to the odd self part of the group. -/
theorem wR8fR88nT_og2 : (oddSumF 64 false wR8fR88nTHX0 (OctadDense.octChunkTerms
    [(wR8fR88nTGT8Labs, wR8fR88nTGT8Nums, 2048), (wR8fR88nTGT9Labs, wR8fR88nTGT9Nums, 2048),
    (wR8fR88nTGT10Labs, wR8fR88nTGT10Nums, 2048), (wR8fR88nTGT11Labs, wR8fR88nTGT11Nums, 2048)]) :
    ℚ) / (2 * (((tensorWordDenAll wR8fR88nTH : ℚ) * 32) / 2 ^ 16)) =
    wR8fR88nTW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wR8fR88nTGT8Labs,
        wR8fR88nTGT8Nums, 2048), (wR8fR88nTGT9Labs, wR8fR88nTGT9Nums, 2048), (wR8fR88nTGT10Labs,
        wR8fR88nTGT10Nums, 2048), (wR8fR88nTGT11Labs, wR8fR88nTGT11Nums, 2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 3: equal to the odd self part of the group. -/
theorem wR8fR88nT_og3 : (oddSumF 64 false wR8fR88nTHX0 (OctadDense.octChunkTerms
    [(wR8fR88nTGT12Labs, wR8fR88nTGT12Nums, 2048), (wR8fR88nTGT13Labs, wR8fR88nTGT13Nums, 2048),
    (wR8fR88nTGT14Labs, wR8fR88nTGT14Nums, 2048), (wR8fR88nTGT15Labs, wR8fR88nTGT15Nums, 2048)]) :
    ℚ) / (2 * (((tensorWordDenAll wR8fR88nTH : ℚ) * 32) / 2 ^ 16)) =
    wR8fR88nTW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wR8fR88nTGT12Labs,
        wR8fR88nTGT12Nums, 2048), (wR8fR88nTGT13Labs, wR8fR88nTGT13Nums, 2048),
        (wR8fR88nTGT14Labs, wR8fR88nTGT14Nums, 2048), (wR8fR88nTGT15Labs, wR8fR88nTGT15Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 4: equal to the odd self part of the group. -/
theorem wR8fR88nT_og4 : (oddSumF 64 false wR8fR88nTHX0 (OctadDense.octChunkTerms
    [(wR8fR88nTGT16Labs, wR8fR88nTGT16Nums, 2048), (wR8fR88nTGT17Labs, wR8fR88nTGT17Nums, 2048),
    (wR8fR88nTGT18Labs, wR8fR88nTGT18Nums, 2048), (wR8fR88nTGT19Labs, wR8fR88nTGT19Nums, 2048)]) :
    ℚ) / (2 * (((tensorWordDenAll wR8fR88nTH : ℚ) * 32) / 2 ^ 16)) =
    wR8fR88nTW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wR8fR88nTGT16Labs,
        wR8fR88nTGT16Nums, 2048), (wR8fR88nTGT17Labs, wR8fR88nTGT17Nums, 2048),
        (wR8fR88nTGT18Labs, wR8fR88nTGT18Nums, 2048), (wR8fR88nTGT19Labs, wR8fR88nTGT19Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 5: equal to the odd self part of the group. -/
theorem wR8fR88nT_og5 : (oddSumF 64 false wR8fR88nTHX0 (OctadDense.octChunkTerms
    [(wR8fR88nTGT20Labs, wR8fR88nTGT20Nums, 2048), (wR8fR88nTGT21Labs, wR8fR88nTGT21Nums, 2048),
    (wR8fR88nTGT22Labs, wR8fR88nTGT22Nums, 1026)]) : ℚ) / (2 * (((tensorWordDenAll wR8fR88nTH : ℚ)
    * 32) / 2 ^ 16)) =
    wR8fR88nTW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wR8fR88nTGT20Labs,
        wR8fR88nTGT20Nums, 2048), (wR8fR88nTGT21Labs, wR8fR88nTGT21Nums, 2048),
        (wR8fR88nTGT22Labs, wR8fR88nTGT22Nums, 1026)])) : ℚ) := by
  decide +kernel

/-- The odd short part equals the odd self part of the target (group checks, no predicted values).
-/
theorem wR8fR88nT_ha : (oddWZ 64 false wR8fR88nTHX0 wR8fR88nTW : ℚ) / (2 * (((tensorWordDenAll
    wR8fR88nTH : ℚ) * 32) / 2 ^ 16)) =
    wR8fR88nTW.sden * (selfOddP wR8fR88nTW : ℚ) :=
  oddPart_of_groups 64 false wR8fR88nTHX0 wR8fR88nTW _ wR8fR88nT_WshG wR8fR88nT_sd
      (((tensorWordDenAll wR8fR88nTH : ℚ) * 32) / 2 ^ 16) (by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [wR8fR88nT_og0, wR8fR88nT_og1, wR8fR88nT_og2, wR8fR88nT_og3, wR8fR88nT_og4,
        wR8fR88nT_og5])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
