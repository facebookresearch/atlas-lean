/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGoctadE18nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGoctadE18nTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (tensor) of the identification Eighth[23]- <-> Tenth[58]- (record goctad:E18-,
e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The source short block as packed chunks. -/
theorem wGoctadXGoctadE18n_LshC : wGoctadXGoctadE18nL.sh = ShortData.ofList
    (OctadDense.octChunkTerms [(wGoctadXGoctadE18nHT0Labs, wGoctadXGoctadE18nHT0Nums, 2048),
    (wGoctadXGoctadE18nHT1Labs, wGoctadXGoctadE18nHT1Nums, 2048), (wGoctadXGoctadE18nHT2Labs,
    wGoctadXGoctadE18nHT2Nums, 2048), (wGoctadXGoctadE18nHT3Labs, wGoctadXGoctadE18nHT3Nums,
    2048), (wGoctadXGoctadE18nHT4Labs, wGoctadXGoctadE18nHT4Nums, 2048),
    (wGoctadXGoctadE18nHT5Labs, wGoctadXGoctadE18nHT5Nums, 2048), (wGoctadXGoctadE18nHT6Labs,
    wGoctadXGoctadE18nHT6Nums, 2048), (wGoctadXGoctadE18nHT7Labs, wGoctadXGoctadE18nHT7Nums,
    2048), (wGoctadXGoctadE18nHT8Labs, wGoctadXGoctadE18nHT8Nums, 2048),
    (wGoctadXGoctadE18nHT9Labs, wGoctadXGoctadE18nHT9Nums, 2048), (wGoctadXGoctadE18nHT10Labs,
    wGoctadXGoctadE18nHT10Nums, 2048), (wGoctadXGoctadE18nHT11Labs, wGoctadXGoctadE18nHT11Nums,
    2048), (wGoctadXGoctadE18nHT12Labs, wGoctadXGoctadE18nHT12Nums, 2048),
    (wGoctadXGoctadE18nHT13Labs, wGoctadXGoctadE18nHT13Nums, 2048), (wGoctadXGoctadE18nHT14Labs,
    wGoctadXGoctadE18nHT14Nums, 2048), (wGoctadXGoctadE18nHT15Labs, wGoctadXGoctadE18nHT15Nums,
    2048), (wGoctadXGoctadE18nHT16Labs, wGoctadXGoctadE18nHT16Nums, 2048),
    (wGoctadXGoctadE18nHT17Labs, wGoctadXGoctadE18nHT17Nums, 2048), (wGoctadXGoctadE18nHT18Labs,
    wGoctadXGoctadE18nHT18Nums, 2048), (wGoctadXGoctadE18nHT19Labs, wGoctadXGoctadE18nHT19Nums,
    2048), (wGoctadXGoctadE18nHT20Labs, wGoctadXGoctadE18nHT20Nums, 2048),
    (wGoctadXGoctadE18nHT21Labs, wGoctadXGoctadE18nHT21Nums, 668)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

set_option maxRecDepth 100000 in
/-- The dense odd tensor part of the source (gident's `OddDense`, one pass over the source
chunks). -/
theorem wGoctadXGoctadE18n_nlchk : OddDense.oddChk 64 ((2 ^ 4 - 1) * 2 ^ 0) true false
    [(wGoctadXGoctadE18nHT0Labs, wGoctadXGoctadE18nHT0Nums, 2048), (wGoctadXGoctadE18nHT1Labs,
    wGoctadXGoctadE18nHT1Nums, 2048), (wGoctadXGoctadE18nHT2Labs, wGoctadXGoctadE18nHT2Nums,
    2048), (wGoctadXGoctadE18nHT3Labs, wGoctadXGoctadE18nHT3Nums, 2048),
    (wGoctadXGoctadE18nHT4Labs, wGoctadXGoctadE18nHT4Nums, 2048), (wGoctadXGoctadE18nHT5Labs,
    wGoctadXGoctadE18nHT5Nums, 2048), (wGoctadXGoctadE18nHT6Labs, wGoctadXGoctadE18nHT6Nums,
    2048), (wGoctadXGoctadE18nHT7Labs, wGoctadXGoctadE18nHT7Nums, 2048),
    (wGoctadXGoctadE18nHT8Labs, wGoctadXGoctadE18nHT8Nums, 2048), (wGoctadXGoctadE18nHT9Labs,
    wGoctadXGoctadE18nHT9Nums, 2048), (wGoctadXGoctadE18nHT10Labs, wGoctadXGoctadE18nHT10Nums,
    2048), (wGoctadXGoctadE18nHT11Labs, wGoctadXGoctadE18nHT11Nums, 2048),
    (wGoctadXGoctadE18nHT12Labs, wGoctadXGoctadE18nHT12Nums, 2048), (wGoctadXGoctadE18nHT13Labs,
    wGoctadXGoctadE18nHT13Nums, 2048), (wGoctadXGoctadE18nHT14Labs, wGoctadXGoctadE18nHT14Nums,
    2048), (wGoctadXGoctadE18nHT15Labs, wGoctadXGoctadE18nHT15Nums, 2048),
    (wGoctadXGoctadE18nHT16Labs, wGoctadXGoctadE18nHT16Nums, 2048), (wGoctadXGoctadE18nHT17Labs,
    wGoctadXGoctadE18nHT17Nums, 2048), (wGoctadXGoctadE18nHT18Labs, wGoctadXGoctadE18nHT18Nums,
    2048), (wGoctadXGoctadE18nHT19Labs, wGoctadXGoctadE18nHT19Nums, 2048),
    (wGoctadXGoctadE18nHT20Labs, wGoctadXGoctadE18nHT20Nums, 2048), (wGoctadXGoctadE18nHT21Labs,
    wGoctadXGoctadE18nHT21Nums, 668)] wGoctadXGoctadE18nGX0 (64256) = true := by
  decide +kernel

/-- The odd tensor part of the source. -/
theorem wGoctadXGoctadE18n_nl : oddLZ 64 false wGoctadXGoctadE18nGX0 wGoctadXGoctadE18nL = 64256 :=
  OddDense.oddLZ_of_chk false wGoctadXGoctadE18nL wGoctadXGoctadE18nW _ wGoctadXGoctadE18n_LshC
      (wGoctadXGoctadE18nGX0_ten ((tensorWordDenAll wGoctadXGoctadE18nG : ℚ) * 32)).symm (by
      decide +kernel)
    (by decide +kernel) wGoctadXGoctadE18nGX0_bnd wGoctadXGoctadE18n_nlchk

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem wGoctadXGoctadE18n_v1 : tdotM 64 (trialityTensorT 64 (!false) wGoctadXGoctadE18nHX0)
    wGoctadXGoctadE18nGX0 = 128512 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor self dot of the target. -/
theorem wGoctadXGoctadE18n_v2 : tdotM 64 wGoctadXGoctadE18nGX0 wGoctadXGoctadE18nGX0 = 128512 :=
    by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wGoctadXGoctadE18n_ht : wGoctadXGoctadE18nL.sden * (oddLZ 64 false wGoctadXGoctadE18nGX0
    wGoctadXGoctadE18nL : ℚ) / (((tensorWordDenAll wGoctadXGoctadE18nG : ℚ) * 32) / 2 ^ 17) +
    (tdotM 64 (trialityTensorT 64 (!false) wGoctadXGoctadE18nHX0) wGoctadXGoctadE18nGX0 : ℚ) / (2
        * (((tensorWordDenAll wGoctadXGoctadE18nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) *
        1))) / 2 ^ 16) * (((tensorWordDenAll wGoctadXGoctadE18nG : ℚ) * 32) / 2 ^ 17)) =
      (tdotM 64 wGoctadXGoctadE18nGX0 wGoctadXGoctadE18nGX0 : ℚ) / ((((tensorWordDenAll
          wGoctadXGoctadE18nG : ℚ) * 32) / 2 ^ 17) * (((tensorWordDenAll wGoctadXGoctadE18nG : ℚ)
          * 32) / 2 ^ 17)) := by
  rw [wGoctadXGoctadE18n_nl, wGoctadXGoctadE18n_v1, wGoctadXGoctadE18n_v2]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
