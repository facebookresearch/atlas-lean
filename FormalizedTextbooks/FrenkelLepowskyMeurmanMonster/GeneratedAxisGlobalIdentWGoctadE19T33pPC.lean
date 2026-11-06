/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE19T33pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE19T33pTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (tensor) of the identification Eighth[24]+ <-> Tenth[61]+ (record
goctad:E19@T33+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The source short block as packed chunks. -/
theorem wGoctadE19T33p_LshC : wGoctadE19T33pL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGoctadE19T33pHT0Labs, wGoctadE19T33pHT0Nums, 2048), (wGoctadE19T33pHT1Labs,
    wGoctadE19T33pHT1Nums, 2048), (wGoctadE19T33pHT2Labs, wGoctadE19T33pHT2Nums, 2048),
    (wGoctadE19T33pHT3Labs, wGoctadE19T33pHT3Nums, 2048), (wGoctadE19T33pHT4Labs,
    wGoctadE19T33pHT4Nums, 2048), (wGoctadE19T33pHT5Labs, wGoctadE19T33pHT5Nums, 2048),
    (wGoctadE19T33pHT6Labs, wGoctadE19T33pHT6Nums, 2048), (wGoctadE19T33pHT7Labs,
    wGoctadE19T33pHT7Nums, 2048), (wGoctadE19T33pHT8Labs, wGoctadE19T33pHT8Nums, 2048),
    (wGoctadE19T33pHT9Labs, wGoctadE19T33pHT9Nums, 2048), (wGoctadE19T33pHT10Labs,
    wGoctadE19T33pHT10Nums, 2048), (wGoctadE19T33pHT11Labs, wGoctadE19T33pHT11Nums, 2048),
    (wGoctadE19T33pHT12Labs, wGoctadE19T33pHT12Nums, 2048), (wGoctadE19T33pHT13Labs,
    wGoctadE19T33pHT13Nums, 2048), (wGoctadE19T33pHT14Labs, wGoctadE19T33pHT14Nums, 2048),
    (wGoctadE19T33pHT15Labs, wGoctadE19T33pHT15Nums, 2048), (wGoctadE19T33pHT16Labs,
    wGoctadE19T33pHT16Nums, 2048), (wGoctadE19T33pHT17Labs, wGoctadE19T33pHT17Nums, 2048),
    (wGoctadE19T33pHT18Labs, wGoctadE19T33pHT18Nums, 2048), (wGoctadE19T33pHT19Labs,
    wGoctadE19T33pHT19Nums, 2048), (wGoctadE19T33pHT20Labs, wGoctadE19T33pHT20Nums, 2048),
    (wGoctadE19T33pHT21Labs, wGoctadE19T33pHT21Nums, 668)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

set_option maxRecDepth 100000 in
/-- The dense odd tensor part of the source (gident's `OddDense`, one pass over the source
chunks). -/
theorem wGoctadE19T33p_nlchk : OddDense.oddChk 64 ((2 ^ 4 - 1) * 2 ^ 0) false true
    [(wGoctadE19T33pHT0Labs, wGoctadE19T33pHT0Nums, 2048), (wGoctadE19T33pHT1Labs,
    wGoctadE19T33pHT1Nums, 2048), (wGoctadE19T33pHT2Labs, wGoctadE19T33pHT2Nums, 2048),
    (wGoctadE19T33pHT3Labs, wGoctadE19T33pHT3Nums, 2048), (wGoctadE19T33pHT4Labs,
    wGoctadE19T33pHT4Nums, 2048), (wGoctadE19T33pHT5Labs, wGoctadE19T33pHT5Nums, 2048),
    (wGoctadE19T33pHT6Labs, wGoctadE19T33pHT6Nums, 2048), (wGoctadE19T33pHT7Labs,
    wGoctadE19T33pHT7Nums, 2048), (wGoctadE19T33pHT8Labs, wGoctadE19T33pHT8Nums, 2048),
    (wGoctadE19T33pHT9Labs, wGoctadE19T33pHT9Nums, 2048), (wGoctadE19T33pHT10Labs,
    wGoctadE19T33pHT10Nums, 2048), (wGoctadE19T33pHT11Labs, wGoctadE19T33pHT11Nums, 2048),
    (wGoctadE19T33pHT12Labs, wGoctadE19T33pHT12Nums, 2048), (wGoctadE19T33pHT13Labs,
    wGoctadE19T33pHT13Nums, 2048), (wGoctadE19T33pHT14Labs, wGoctadE19T33pHT14Nums, 2048),
    (wGoctadE19T33pHT15Labs, wGoctadE19T33pHT15Nums, 2048), (wGoctadE19T33pHT16Labs,
    wGoctadE19T33pHT16Nums, 2048), (wGoctadE19T33pHT17Labs, wGoctadE19T33pHT17Nums, 2048),
    (wGoctadE19T33pHT18Labs, wGoctadE19T33pHT18Nums, 2048), (wGoctadE19T33pHT19Labs,
    wGoctadE19T33pHT19Nums, 2048), (wGoctadE19T33pHT20Labs, wGoctadE19T33pHT20Nums, 2048),
    (wGoctadE19T33pHT21Labs, wGoctadE19T33pHT21Nums, 668)] wGoctadE19T33pGX0 (65024) = true := by
  decide +kernel

/-- The odd tensor part of the source. -/
theorem wGoctadE19T33p_nl : oddLZ 64 true wGoctadE19T33pGX0 wGoctadE19T33pL = 65024 :=
  OddDense.oddLZ_of_chk true wGoctadE19T33pL wGoctadE19T33pW _ wGoctadE19T33p_LshC
      (wGoctadE19T33pGX0_ten ((tensorWordDenAll wGoctadE19T33pG : ℚ) * 32)).symm (by
      decide +kernel)
    (by decide +kernel) wGoctadE19T33pGX0_bnd wGoctadE19T33p_nlchk

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem wGoctadE19T33p_v1 : tdotM 64 (trialityTensorT 64 (!true) wGoctadE19T33pHX0)
    wGoctadE19T33pGX0 = 126976 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor self dot of the target. -/
theorem wGoctadE19T33p_v2 : tdotM 64 wGoctadE19T33pGX0 wGoctadE19T33pGX0 = 128512 := by
    decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wGoctadE19T33p_ht : wGoctadE19T33pL.sden * (oddLZ 64 true wGoctadE19T33pGX0
    wGoctadE19T33pL : ℚ) / (((tensorWordDenAll wGoctadE19T33pG : ℚ) * 32) / 2 ^ 17) +
    (tdotM 64 (trialityTensorT 64 (!true) wGoctadE19T33pHX0) wGoctadE19T33pGX0 : ℚ) / (2 *
        (((tensorWordDenAll wGoctadE19T33pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)))
        / 2 ^ 25) * (((tensorWordDenAll wGoctadE19T33pG : ℚ) * 32) / 2 ^ 17)) =
      (tdotM 64 wGoctadE19T33pGX0 wGoctadE19T33pGX0 : ℚ) / ((((tensorWordDenAll wGoctadE19T33pG :
          ℚ) * 32) / 2 ^ 17) * (((tensorWordDenAll wGoctadE19T33pG : ℚ) * 32) / 2 ^ 17)) := by
  rw [wGoctadE19T33p_nl, wGoctadE19T33p_v1, wGoctadE19T33p_v2]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
