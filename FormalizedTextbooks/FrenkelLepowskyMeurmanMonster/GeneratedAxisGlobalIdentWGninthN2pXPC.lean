/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN2pXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN2pXTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (tensor) of the identification Ninth[3]+ <-> Tenth[50]+ (record gninth:N2+, e
= 1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The source short block as packed chunks. -/
theorem wGninthN2pX_LshC : wGninthN2pXL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN2pXHT0Labs, wGninthN2pXHT0Nums, 2048), (wGninthN2pXHT1Labs, wGninthN2pXHT1Nums,
    2048), (wGninthN2pXHT2Labs, wGninthN2pXHT2Nums, 2048), (wGninthN2pXHT3Labs,
    wGninthN2pXHT3Nums, 2048), (wGninthN2pXHT4Labs, wGninthN2pXHT4Nums, 2048),
    (wGninthN2pXHT5Labs, wGninthN2pXHT5Nums, 2048), (wGninthN2pXHT6Labs, wGninthN2pXHT6Nums,
    2048), (wGninthN2pXHT7Labs, wGninthN2pXHT7Nums, 2048), (wGninthN2pXHT8Labs,
    wGninthN2pXHT8Nums, 2048), (wGninthN2pXHT9Labs, wGninthN2pXHT9Nums, 2048),
    (wGninthN2pXHT10Labs, wGninthN2pXHT10Nums, 2048), (wGninthN2pXHT11Labs, wGninthN2pXHT11Nums,
    2048), (wGninthN2pXHT12Labs, wGninthN2pXHT12Nums, 2048), (wGninthN2pXHT13Labs,
    wGninthN2pXHT13Nums, 2048), (wGninthN2pXHT14Labs, wGninthN2pXHT14Nums, 2048),
    (wGninthN2pXHT15Labs, wGninthN2pXHT15Nums, 2048), (wGninthN2pXHT16Labs, wGninthN2pXHT16Nums,
    2048), (wGninthN2pXHT17Labs, wGninthN2pXHT17Nums, 2048), (wGninthN2pXHT18Labs,
    wGninthN2pXHT18Nums, 2048), (wGninthN2pXHT19Labs, wGninthN2pXHT19Nums, 2048),
    (wGninthN2pXHT20Labs, wGninthN2pXHT20Nums, 2048), (wGninthN2pXHT21Labs, wGninthN2pXHT21Nums,
    2048), (wGninthN2pXHT22Labs, wGninthN2pXHT22Nums, 2048), (wGninthN2pXHT23Labs,
    wGninthN2pXHT23Nums, 2048), (wGninthN2pXHT24Labs, wGninthN2pXHT24Nums, 2048),
    (wGninthN2pXHT25Labs, wGninthN2pXHT25Nums, 2048), (wGninthN2pXHT26Labs, wGninthN2pXHT26Nums,
    2048), (wGninthN2pXHT27Labs, wGninthN2pXHT27Nums, 2048), (wGninthN2pXHT28Labs,
    wGninthN2pXHT28Nums, 2048), (wGninthN2pXHT29Labs, wGninthN2pXHT29Nums, 2048),
    (wGninthN2pXHT30Labs, wGninthN2pXHT30Nums, 144)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

set_option maxRecDepth 100000 in
/-- The dense odd tensor part of the source (gident's `OddDense`, one pass over the source
chunks). -/
theorem wGninthN2pX_nlchk : OddDense.oddChk 64 ((2 ^ 4 - 1) * 2 ^ 0) false true
    [(wGninthN2pXHT0Labs, wGninthN2pXHT0Nums, 2048), (wGninthN2pXHT1Labs, wGninthN2pXHT1Nums,
    2048), (wGninthN2pXHT2Labs, wGninthN2pXHT2Nums, 2048), (wGninthN2pXHT3Labs,
    wGninthN2pXHT3Nums, 2048), (wGninthN2pXHT4Labs, wGninthN2pXHT4Nums, 2048),
    (wGninthN2pXHT5Labs, wGninthN2pXHT5Nums, 2048), (wGninthN2pXHT6Labs, wGninthN2pXHT6Nums,
    2048), (wGninthN2pXHT7Labs, wGninthN2pXHT7Nums, 2048), (wGninthN2pXHT8Labs,
    wGninthN2pXHT8Nums, 2048), (wGninthN2pXHT9Labs, wGninthN2pXHT9Nums, 2048),
    (wGninthN2pXHT10Labs, wGninthN2pXHT10Nums, 2048), (wGninthN2pXHT11Labs, wGninthN2pXHT11Nums,
    2048), (wGninthN2pXHT12Labs, wGninthN2pXHT12Nums, 2048), (wGninthN2pXHT13Labs,
    wGninthN2pXHT13Nums, 2048), (wGninthN2pXHT14Labs, wGninthN2pXHT14Nums, 2048),
    (wGninthN2pXHT15Labs, wGninthN2pXHT15Nums, 2048), (wGninthN2pXHT16Labs, wGninthN2pXHT16Nums,
    2048), (wGninthN2pXHT17Labs, wGninthN2pXHT17Nums, 2048), (wGninthN2pXHT18Labs,
    wGninthN2pXHT18Nums, 2048), (wGninthN2pXHT19Labs, wGninthN2pXHT19Nums, 2048),
    (wGninthN2pXHT20Labs, wGninthN2pXHT20Nums, 2048), (wGninthN2pXHT21Labs, wGninthN2pXHT21Nums,
    2048), (wGninthN2pXHT22Labs, wGninthN2pXHT22Nums, 2048), (wGninthN2pXHT23Labs,
    wGninthN2pXHT23Nums, 2048), (wGninthN2pXHT24Labs, wGninthN2pXHT24Nums, 2048),
    (wGninthN2pXHT25Labs, wGninthN2pXHT25Nums, 2048), (wGninthN2pXHT26Labs, wGninthN2pXHT26Nums,
    2048), (wGninthN2pXHT27Labs, wGninthN2pXHT27Nums, 2048), (wGninthN2pXHT28Labs,
    wGninthN2pXHT28Nums, 2048), (wGninthN2pXHT29Labs, wGninthN2pXHT29Nums, 2048),
    (wGninthN2pXHT30Labs, wGninthN2pXHT30Nums, 144)] wGninthN2pXGX0 (256000) = true := by
  decide +kernel

/-- The odd tensor part of the source. -/
theorem wGninthN2pX_nl : oddLZ 64 true wGninthN2pXGX0 wGninthN2pXL = 256000 :=
  OddDense.oddLZ_of_chk true wGninthN2pXL wGninthN2pXW _ wGninthN2pX_LshC (wGninthN2pXGX0_ten
      ((tensorWordDenAll wGninthN2pXG : ℚ) * 32)).symm (by decide +kernel)
    (by decide +kernel) wGninthN2pXGX0_bnd wGninthN2pX_nlchk

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem wGninthN2pX_v1 : tdotM 64 (trialityTensorT 64 (!true) wGninthN2pXHX0) wGninthN2pXGX0 =
    129024 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor self dot of the target. -/
theorem wGninthN2pX_v2 : tdotM 64 wGninthN2pXGX0 wGninthN2pXGX0 = 128512 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wGninthN2pX_ht : wGninthN2pXL.sden * (oddLZ 64 true wGninthN2pXGX0 wGninthN2pXL : ℚ) /
    (((tensorWordDenAll wGninthN2pXG : ℚ) * 32) / 2 ^ 25) +
    (tdotM 64 (trialityTensorT 64 (!true) wGninthN2pXHX0) wGninthN2pXGX0 : ℚ) / (2 *
        (((tensorWordDenAll wGninthN2pXH : ℚ) * 32) / 2 ^ 8) * (((tensorWordDenAll wGninthN2pXG :
        ℚ) * 32) / 2 ^ 25)) =
      (tdotM 64 wGninthN2pXGX0 wGninthN2pXGX0 : ℚ) / ((((tensorWordDenAll wGninthN2pXG : ℚ) * 32)
          / 2 ^ 25) * (((tensorWordDenAll wGninthN2pXG : ℚ) * 32) / 2 ^ 25)) := by
  rw [wGninthN2pX_nl, wGninthN2pX_v1, wGninthN2pX_v2]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
