/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN7nXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN7nXTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (odd short terms) of the identification Fifth[4]+ <-> Ninth[12]- (record
gninth:N7-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target short block as packed chunks, in groups. -/
theorem wGninthN7nX_WshG : wGninthN7nXW.sh = ShortData.ofList [OctadDense.octChunkTerms
    [(wGninthN7nXGT0Labs, wGninthN7nXGT0Nums, 2048), (wGninthN7nXGT1Labs, wGninthN7nXGT1Nums,
    2048), (wGninthN7nXGT2Labs, wGninthN7nXGT2Nums, 40)]].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, OctadDense.octChunkTerms]
  rfl

set_option maxRecDepth 100000 in
/-- The odd labels of the target are distinct. -/
theorem wGninthN7nX_sd : labDistinct wGninthN7nXW.sh.odd 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part, target chunk group 0: equal to the odd self part of the group. -/
theorem wGninthN7nX_og0 : (oddSumF 64 false wGninthN7nXHX0 (OctadDense.octChunkTerms
    [(wGninthN7nXGT0Labs, wGninthN7nXGT0Nums, 2048), (wGninthN7nXGT1Labs, wGninthN7nXGT1Nums,
    2048), (wGninthN7nXGT2Labs, wGninthN7nXGT2Nums, 40)]) : ℚ) / (2 * (((tensorWordDenAll
    wGninthN7nXH : ℚ) * 32) / 2 ^ 16)) =
    wGninthN7nXW.sden * (sqSumZ (oddsOf (OctadDense.octChunkTerms [(wGninthN7nXGT0Labs,
        wGninthN7nXGT0Nums, 2048), (wGninthN7nXGT1Labs, wGninthN7nXGT1Nums, 2048),
        (wGninthN7nXGT2Labs, wGninthN7nXGT2Nums, 40)])) : ℚ) := by
  decide +kernel

/-- The odd short part equals the odd self part of the target (group checks, no predicted values).
-/
theorem wGninthN7nX_ha : (oddWZ 64 false wGninthN7nXHX0 wGninthN7nXW : ℚ) / (2 *
    (((tensorWordDenAll wGninthN7nXH : ℚ) * 32) / 2 ^ 16)) =
    wGninthN7nXW.sden * (selfOddP wGninthN7nXW : ℚ) :=
  oddPart_of_groups 64 false wGninthN7nXHX0 wGninthN7nXW _ wGninthN7nX_WshG wGninthN7nX_sd
      (((tensorWordDenAll wGninthN7nXH : ℚ) * 32) / 2 ^ 16) (by
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl
    exacts [wGninthN7nX_og0])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
