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

/-! # Factory parts (tensor) of the identification Sixth[8]- <-> Tenth[73]+ (record gforest:S6c4-,
e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The source short block as packed chunks. -/
theorem wGoctadXGforestS6c4n_LshC : wGoctadXGforestS6c4nL.sh = ShortData.ofList
    (OctadDense.octChunkTerms [(wGoctadXGforestS6c4nHT0Labs, wGoctadXGforestS6c4nHT0Nums, 2048),
    (wGoctadXGforestS6c4nHT1Labs, wGoctadXGforestS6c4nHT1Nums, 2048),
    (wGoctadXGforestS6c4nHT2Labs, wGoctadXGforestS6c4nHT2Nums, 2048),
    (wGoctadXGforestS6c4nHT3Labs, wGoctadXGforestS6c4nHT3Nums, 2048),
    (wGoctadXGforestS6c4nHT4Labs, wGoctadXGforestS6c4nHT4Nums, 2048),
    (wGoctadXGforestS6c4nHT5Labs, wGoctadXGforestS6c4nHT5Nums, 2048),
    (wGoctadXGforestS6c4nHT6Labs, wGoctadXGforestS6c4nHT6Nums, 2048),
    (wGoctadXGforestS6c4nHT7Labs, wGoctadXGforestS6c4nHT7Nums, 2048),
    (wGoctadXGforestS6c4nHT8Labs, wGoctadXGforestS6c4nHT8Nums, 2048),
    (wGoctadXGforestS6c4nHT9Labs, wGoctadXGforestS6c4nHT9Nums, 2048),
    (wGoctadXGforestS6c4nHT10Labs, wGoctadXGforestS6c4nHT10Nums, 2048),
    (wGoctadXGforestS6c4nHT11Labs, wGoctadXGforestS6c4nHT11Nums, 2048),
    (wGoctadXGforestS6c4nHT12Labs, wGoctadXGforestS6c4nHT12Nums, 2048),
    (wGoctadXGforestS6c4nHT13Labs, wGoctadXGforestS6c4nHT13Nums, 2048),
    (wGoctadXGforestS6c4nHT14Labs, wGoctadXGforestS6c4nHT14Nums, 1640)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

set_option maxRecDepth 100000 in
/-- The dense odd tensor part of the source (gident's `OddDense`, one pass over the source
chunks). -/
theorem wGoctadXGforestS6c4n_nlchk : OddDense.oddChk 64 ((2 ^ 5 - 1) * 2 ^ 0) true false
    [(wGoctadXGforestS6c4nHT0Labs, wGoctadXGforestS6c4nHT0Nums, 2048),
    (wGoctadXGforestS6c4nHT1Labs, wGoctadXGforestS6c4nHT1Nums, 2048),
    (wGoctadXGforestS6c4nHT2Labs, wGoctadXGforestS6c4nHT2Nums, 2048),
    (wGoctadXGforestS6c4nHT3Labs, wGoctadXGforestS6c4nHT3Nums, 2048),
    (wGoctadXGforestS6c4nHT4Labs, wGoctadXGforestS6c4nHT4Nums, 2048),
    (wGoctadXGforestS6c4nHT5Labs, wGoctadXGforestS6c4nHT5Nums, 2048),
    (wGoctadXGforestS6c4nHT6Labs, wGoctadXGforestS6c4nHT6Nums, 2048),
    (wGoctadXGforestS6c4nHT7Labs, wGoctadXGforestS6c4nHT7Nums, 2048),
    (wGoctadXGforestS6c4nHT8Labs, wGoctadXGforestS6c4nHT8Nums, 2048),
    (wGoctadXGforestS6c4nHT9Labs, wGoctadXGforestS6c4nHT9Nums, 2048),
    (wGoctadXGforestS6c4nHT10Labs, wGoctadXGforestS6c4nHT10Nums, 2048),
    (wGoctadXGforestS6c4nHT11Labs, wGoctadXGforestS6c4nHT11Nums, 2048),
    (wGoctadXGforestS6c4nHT12Labs, wGoctadXGforestS6c4nHT12Nums, 2048),
    (wGoctadXGforestS6c4nHT13Labs, wGoctadXGforestS6c4nHT13Nums, 2048),
    (wGoctadXGforestS6c4nHT14Labs, wGoctadXGforestS6c4nHT14Nums, 1640)] wGoctadXGforestS6c4nGX0
    (66304) = true := by
  decide +kernel

/-- The odd tensor part of the source. -/
theorem wGoctadXGforestS6c4n_nl : oddLZ 64 false wGoctadXGforestS6c4nGX0 wGoctadXGforestS6c4nL =
    66304 :=
  OddDense.oddLZ_of_chk false wGoctadXGforestS6c4nL wGoctadXGforestS6c4nW _
      wGoctadXGforestS6c4n_LshC (wGoctadXGforestS6c4nGX0_ten ((tensorWordDenAll
      wGoctadXGforestS6c4nG : ℚ) * 32)).symm (by decide +kernel)
    (by decide +kernel) wGoctadXGforestS6c4nGX0_bnd wGoctadXGforestS6c4n_nlchk

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem wGoctadXGforestS6c4n_v1 : tdotM 64 (trialityTensorT 64 (!false) wGoctadXGforestS6c4nHX0)
    wGoctadXGforestS6c4nGX0 = 124416 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor self dot of the target. -/
theorem wGoctadXGforestS6c4n_v2 : tdotM 64 wGoctadXGforestS6c4nGX0 wGoctadXGforestS6c4nGX0 =
    128512 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wGoctadXGforestS6c4n_ht : wGoctadXGforestS6c4nL.sden * (oddLZ 64 false
    wGoctadXGforestS6c4nGX0 wGoctadXGforestS6c4nL : ℚ) / (((tensorWordDenAll wGoctadXGforestS6c4nG
    : ℚ) * 32) / 2 ^ 13) +
    (tdotM 64 (trialityTensorT 64 (!false) wGoctadXGforestS6c4nHX0) wGoctadXGforestS6c4nGX0 : ℚ) /
        (2 * (((tensorWordDenAll wGoctadXGforestS6c4nH : ℚ) * 32) / 2 ^ 12) * (((tensorWordDenAll
        wGoctadXGforestS6c4nG : ℚ) * 32) / 2 ^ 13)) =
      (tdotM 64 wGoctadXGforestS6c4nGX0 wGoctadXGforestS6c4nGX0 : ℚ) / ((((tensorWordDenAll
          wGoctadXGforestS6c4nG : ℚ) * 32) / 2 ^ 13) * (((tensorWordDenAll wGoctadXGforestS6c4nG :
          ℚ) * 32) / 2 ^ 13)) := by
  rw [wGoctadXGforestS6c4n_nl, wGoctadXGforestS6c4n_v1, wGoctadXGforestS6c4n_v2]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
