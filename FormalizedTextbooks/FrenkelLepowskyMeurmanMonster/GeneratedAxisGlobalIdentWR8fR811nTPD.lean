/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR811nTChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR811nTTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (odd short terms) of the identification Root8[13]- <-> Root8[13]- (record
r8f:R811-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target short block as packed chunks, in groups. -/
theorem wR8fR811nT_WshG : wR8fR811nTW.sh = ShortData.ofList [OctadDense.octChunkTerms
    [(wR8fR811nTGT0Labs, wR8fR811nTGT0Nums, 2048), (wR8fR811nTGT1Labs, wR8fR811nTGT1Nums, 2048),
    (wR8fR811nTGT2Labs, wR8fR811nTGT2Nums, 2048), (wR8fR811nTGT3Labs, wR8fR811nTGT3Nums, 2048)],
    OctadDense.octChunkTerms [(wR8fR811nTGT4Labs, wR8fR811nTGT4Nums, 2048), (wR8fR811nTGT5Labs,
    wR8fR811nTGT5Nums, 2048), (wR8fR811nTGT6Labs, wR8fR811nTGT6Nums, 2048), (wR8fR811nTGT7Labs,
    wR8fR811nTGT7Nums, 2048)], OctadDense.octChunkTerms [(wR8fR811nTGT8Labs, wR8fR811nTGT8Nums,
    2048), (wR8fR811nTGT9Labs, wR8fR811nTGT9Nums, 2048), (wR8fR811nTGT10Labs, wR8fR811nTGT10Nums,
    2048), (wR8fR811nTGT11Labs, wR8fR811nTGT11Nums, 2048)], OctadDense.octChunkTerms
    [(wR8fR811nTGT12Labs, wR8fR811nTGT12Nums, 2048), (wR8fR811nTGT13Labs, wR8fR811nTGT13Nums,
    2048), (wR8fR811nTGT14Labs, wR8fR811nTGT14Nums, 2048), (wR8fR811nTGT15Labs,
    wR8fR811nTGT15Nums, 2048)], OctadDense.octChunkTerms [(wR8fR811nTGT16Labs, wR8fR811nTGT16Nums,
    808)]].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, OctadDense.octChunkTerms,
    List.append_assoc]
  rfl

set_option maxRecDepth 100000 in
/-- The odd labels of the target are distinct. -/
theorem wR8fR811nT_sd : labDistinct wR8fR811nTW.sh.odd 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 0: equal to the odd self part of the group. -/
theorem wR8fR811nT_og0 : (oddSumF 64 false wR8fR811nTHX0 (OctadDense.octChunkTerms
    [(wR8fR811nTGT0Labs, wR8fR811nTGT0Nums, 2048), (wR8fR811nTGT1Labs, wR8fR811nTGT1Nums, 2048),
    (wR8fR811nTGT2Labs, wR8fR811nTGT2Nums, 2048), (wR8fR811nTGT3Labs, wR8fR811nTGT3Nums, 2048)]) :
    ℚ) / (2 * (((tensorWordDenAll wR8fR811nTH : ℚ) * 32) / 2 ^ 13)) =
    wR8fR811nTW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wR8fR811nTGT0Labs,
        wR8fR811nTGT0Nums, 2048), (wR8fR811nTGT1Labs, wR8fR811nTGT1Nums, 2048),
        (wR8fR811nTGT2Labs, wR8fR811nTGT2Nums, 2048), (wR8fR811nTGT3Labs, wR8fR811nTGT3Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 1: equal to the odd self part of the group. -/
theorem wR8fR811nT_og1 : (oddSumF 64 false wR8fR811nTHX0 (OctadDense.octChunkTerms
    [(wR8fR811nTGT4Labs, wR8fR811nTGT4Nums, 2048), (wR8fR811nTGT5Labs, wR8fR811nTGT5Nums, 2048),
    (wR8fR811nTGT6Labs, wR8fR811nTGT6Nums, 2048), (wR8fR811nTGT7Labs, wR8fR811nTGT7Nums, 2048)]) :
    ℚ) / (2 * (((tensorWordDenAll wR8fR811nTH : ℚ) * 32) / 2 ^ 13)) =
    wR8fR811nTW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wR8fR811nTGT4Labs,
        wR8fR811nTGT4Nums, 2048), (wR8fR811nTGT5Labs, wR8fR811nTGT5Nums, 2048),
        (wR8fR811nTGT6Labs, wR8fR811nTGT6Nums, 2048), (wR8fR811nTGT7Labs, wR8fR811nTGT7Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 2: equal to the odd self part of the group. -/
theorem wR8fR811nT_og2 : (oddSumF 64 false wR8fR811nTHX0 (OctadDense.octChunkTerms
    [(wR8fR811nTGT8Labs, wR8fR811nTGT8Nums, 2048), (wR8fR811nTGT9Labs, wR8fR811nTGT9Nums, 2048),
    (wR8fR811nTGT10Labs, wR8fR811nTGT10Nums, 2048), (wR8fR811nTGT11Labs, wR8fR811nTGT11Nums,
    2048)]) : ℚ) / (2 * (((tensorWordDenAll wR8fR811nTH : ℚ) * 32) / 2 ^ 13)) =
    wR8fR811nTW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wR8fR811nTGT8Labs,
        wR8fR811nTGT8Nums, 2048), (wR8fR811nTGT9Labs, wR8fR811nTGT9Nums, 2048),
        (wR8fR811nTGT10Labs, wR8fR811nTGT10Nums, 2048), (wR8fR811nTGT11Labs, wR8fR811nTGT11Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 3: equal to the odd self part of the group. -/
theorem wR8fR811nT_og3 : (oddSumF 64 false wR8fR811nTHX0 (OctadDense.octChunkTerms
    [(wR8fR811nTGT12Labs, wR8fR811nTGT12Nums, 2048), (wR8fR811nTGT13Labs, wR8fR811nTGT13Nums,
    2048), (wR8fR811nTGT14Labs, wR8fR811nTGT14Nums, 2048), (wR8fR811nTGT15Labs,
    wR8fR811nTGT15Nums, 2048)]) : ℚ) / (2 * (((tensorWordDenAll wR8fR811nTH : ℚ) * 32) / 2 ^ 13))
    =
    wR8fR811nTW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wR8fR811nTGT12Labs,
        wR8fR811nTGT12Nums, 2048), (wR8fR811nTGT13Labs, wR8fR811nTGT13Nums, 2048),
        (wR8fR811nTGT14Labs, wR8fR811nTGT14Nums, 2048), (wR8fR811nTGT15Labs, wR8fR811nTGT15Nums,
        2048)])) : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 4: equal to the odd self part of the group. -/
theorem wR8fR811nT_og4 : (oddSumF 64 false wR8fR811nTHX0 (OctadDense.octChunkTerms
    [(wR8fR811nTGT16Labs, wR8fR811nTGT16Nums, 808)]) : ℚ) / (2 * (((tensorWordDenAll wR8fR811nTH :
    ℚ) * 32) / 2 ^ 13)) =
    wR8fR811nTW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wR8fR811nTGT16Labs,
        wR8fR811nTGT16Nums, 808)])) : ℚ) := by
  decide +kernel

/-- The odd short part equals the odd self part of the target (group checks, no predicted values).
-/
theorem wR8fR811nT_ha : (oddWZ 64 false wR8fR811nTHX0 wR8fR811nTW : ℚ) / (2 * (((tensorWordDenAll
    wR8fR811nTH : ℚ) * 32) / 2 ^ 13)) =
    wR8fR811nTW.sden * (selfOddP wR8fR811nTW : ℚ) :=
  oddPart_of_groups 64 false wR8fR811nTHX0 wR8fR811nTW _ wR8fR811nT_WshG wR8fR811nT_sd
      (((tensorWordDenAll wR8fR811nTH : ℚ) * 32) / 2 ^ 13) (by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl
    exacts [wR8fR811nT_og0, wR8fR811nT_og1, wR8fR811nT_og2, wR8fR811nT_og3, wR8fR811nT_og4])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
