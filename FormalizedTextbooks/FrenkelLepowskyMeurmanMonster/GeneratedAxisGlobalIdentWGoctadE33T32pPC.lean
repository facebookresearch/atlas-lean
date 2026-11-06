/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE33T32pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE33T32pTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (tensor) of the identification Eighth[46]+ <-> Tenth[46]+ (record
goctad:E33@T32+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The source short block as packed chunks. -/
theorem wGoctadE33T32p_LshC : wGoctadE33T32pL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGoctadE33T32pHT0Labs, wGoctadE33T32pHT0Nums, 2048), (wGoctadE33T32pHT1Labs,
    wGoctadE33T32pHT1Nums, 2048), (wGoctadE33T32pHT2Labs, wGoctadE33T32pHT2Nums, 2048),
    (wGoctadE33T32pHT3Labs, wGoctadE33T32pHT3Nums, 2048), (wGoctadE33T32pHT4Labs,
    wGoctadE33T32pHT4Nums, 2048), (wGoctadE33T32pHT5Labs, wGoctadE33T32pHT5Nums, 2048),
    (wGoctadE33T32pHT6Labs, wGoctadE33T32pHT6Nums, 2048), (wGoctadE33T32pHT7Labs,
    wGoctadE33T32pHT7Nums, 2048), (wGoctadE33T32pHT8Labs, wGoctadE33T32pHT8Nums, 2048),
    (wGoctadE33T32pHT9Labs, wGoctadE33T32pHT9Nums, 2048), (wGoctadE33T32pHT10Labs,
    wGoctadE33T32pHT10Nums, 2048), (wGoctadE33T32pHT11Labs, wGoctadE33T32pHT11Nums, 2048),
    (wGoctadE33T32pHT12Labs, wGoctadE33T32pHT12Nums, 2048), (wGoctadE33T32pHT13Labs,
    wGoctadE33T32pHT13Nums, 2048), (wGoctadE33T32pHT14Labs, wGoctadE33T32pHT14Nums, 2048),
    (wGoctadE33T32pHT15Labs, wGoctadE33T32pHT15Nums, 2048), (wGoctadE33T32pHT16Labs,
    wGoctadE33T32pHT16Nums, 2048), (wGoctadE33T32pHT17Labs, wGoctadE33T32pHT17Nums, 2048),
    (wGoctadE33T32pHT18Labs, wGoctadE33T32pHT18Nums, 2048), (wGoctadE33T32pHT19Labs,
    wGoctadE33T32pHT19Nums, 2048), (wGoctadE33T32pHT20Labs, wGoctadE33T32pHT20Nums, 2048),
    (wGoctadE33T32pHT21Labs, wGoctadE33T32pHT21Nums, 668)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

set_option maxRecDepth 100000 in
/-- The dense odd tensor part of the source (gident's `OddDense`, one pass over the source
chunks). -/
theorem wGoctadE33T32p_nlchk : OddDense.oddChk 80 ((2 ^ 4 - 1) * 2 ^ 0) false true
    [(wGoctadE33T32pHT0Labs, wGoctadE33T32pHT0Nums, 2048), (wGoctadE33T32pHT1Labs,
    wGoctadE33T32pHT1Nums, 2048), (wGoctadE33T32pHT2Labs, wGoctadE33T32pHT2Nums, 2048),
    (wGoctadE33T32pHT3Labs, wGoctadE33T32pHT3Nums, 2048), (wGoctadE33T32pHT4Labs,
    wGoctadE33T32pHT4Nums, 2048), (wGoctadE33T32pHT5Labs, wGoctadE33T32pHT5Nums, 2048),
    (wGoctadE33T32pHT6Labs, wGoctadE33T32pHT6Nums, 2048), (wGoctadE33T32pHT7Labs,
    wGoctadE33T32pHT7Nums, 2048), (wGoctadE33T32pHT8Labs, wGoctadE33T32pHT8Nums, 2048),
    (wGoctadE33T32pHT9Labs, wGoctadE33T32pHT9Nums, 2048), (wGoctadE33T32pHT10Labs,
    wGoctadE33T32pHT10Nums, 2048), (wGoctadE33T32pHT11Labs, wGoctadE33T32pHT11Nums, 2048),
    (wGoctadE33T32pHT12Labs, wGoctadE33T32pHT12Nums, 2048), (wGoctadE33T32pHT13Labs,
    wGoctadE33T32pHT13Nums, 2048), (wGoctadE33T32pHT14Labs, wGoctadE33T32pHT14Nums, 2048),
    (wGoctadE33T32pHT15Labs, wGoctadE33T32pHT15Nums, 2048), (wGoctadE33T32pHT16Labs,
    wGoctadE33T32pHT16Nums, 2048), (wGoctadE33T32pHT17Labs, wGoctadE33T32pHT17Nums, 2048),
    (wGoctadE33T32pHT18Labs, wGoctadE33T32pHT18Nums, 2048), (wGoctadE33T32pHT19Labs,
    wGoctadE33T32pHT19Nums, 2048), (wGoctadE33T32pHT20Labs, wGoctadE33T32pHT20Nums, 2048),
    (wGoctadE33T32pHT21Labs, wGoctadE33T32pHT21Nums, 668)] wGoctadE33T32pGX0 (65024) = true := by
  decide +kernel

/-- The odd tensor part of the source. -/
theorem wGoctadE33T32p_nl : oddLZ 80 true wGoctadE33T32pGX0 wGoctadE33T32pL = 65024 :=
  OddDense.oddLZ_of_chk true wGoctadE33T32pL wGoctadE33T32pW _ wGoctadE33T32p_LshC
      (wGoctadE33T32pGX0_ten ((tensorWordDenAll wGoctadE33T32pG : ℚ) * 32)).symm (by
      decide +kernel)
    (by decide +kernel) wGoctadE33T32pGX0_bnd wGoctadE33T32p_nlchk

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem wGoctadE33T32p_v1 : tdotM 80 (trialityTensorT 80 (!true) wGoctadE33T32pHX0)
    wGoctadE33T32pGX0 = 126976 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor self dot of the target. -/
theorem wGoctadE33T32p_v2 : tdotM 80 wGoctadE33T32pGX0 wGoctadE33T32pGX0 = 128512 := by
    decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wGoctadE33T32p_ht : wGoctadE33T32pL.sden * (oddLZ 80 true wGoctadE33T32pGX0
    wGoctadE33T32pL : ℚ) / (((tensorWordDenAll wGoctadE33T32pG : ℚ) * 32) / 2 ^ 13) +
    (tdotM 80 (trialityTensorT 80 (!true) wGoctadE33T32pHX0) wGoctadE33T32pGX0 : ℚ) / (2 *
        (((tensorWordDenAll wGoctadE33T32pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)))
        / 2 ^ 37) * (((tensorWordDenAll wGoctadE33T32pG : ℚ) * 32) / 2 ^ 13)) =
      (tdotM 80 wGoctadE33T32pGX0 wGoctadE33T32pGX0 : ℚ) / ((((tensorWordDenAll wGoctadE33T32pG :
          ℚ) * 32) / 2 ^ 13) * (((tensorWordDenAll wGoctadE33T32pG : ℚ) * 32) / 2 ^ 13)) := by
  rw [wGoctadE33T32p_nl, wGoctadE33T32p_v1, wGoctadE33T32p_v2]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
