/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN4pXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN4pXTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (tensor) of the identification Ninth[6]+ <-> Tenth[74]- (record gninth:N4+, e
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
theorem wGninthN4pX_LshC : wGninthN4pXL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN4pXHT0Labs, wGninthN4pXHT0Nums, 2048), (wGninthN4pXHT1Labs, wGninthN4pXHT1Nums,
    2048), (wGninthN4pXHT2Labs, wGninthN4pXHT2Nums, 2048), (wGninthN4pXHT3Labs,
    wGninthN4pXHT3Nums, 2048), (wGninthN4pXHT4Labs, wGninthN4pXHT4Nums, 2048),
    (wGninthN4pXHT5Labs, wGninthN4pXHT5Nums, 2048), (wGninthN4pXHT6Labs, wGninthN4pXHT6Nums,
    2048), (wGninthN4pXHT7Labs, wGninthN4pXHT7Nums, 2048), (wGninthN4pXHT8Labs,
    wGninthN4pXHT8Nums, 2048), (wGninthN4pXHT9Labs, wGninthN4pXHT9Nums, 2048),
    (wGninthN4pXHT10Labs, wGninthN4pXHT10Nums, 2048), (wGninthN4pXHT11Labs, wGninthN4pXHT11Nums,
    2048), (wGninthN4pXHT12Labs, wGninthN4pXHT12Nums, 2048), (wGninthN4pXHT13Labs,
    wGninthN4pXHT13Nums, 2048), (wGninthN4pXHT14Labs, wGninthN4pXHT14Nums, 2048),
    (wGninthN4pXHT15Labs, wGninthN4pXHT15Nums, 2048), (wGninthN4pXHT16Labs, wGninthN4pXHT16Nums,
    2048), (wGninthN4pXHT17Labs, wGninthN4pXHT17Nums, 2048), (wGninthN4pXHT18Labs,
    wGninthN4pXHT18Nums, 2048), (wGninthN4pXHT19Labs, wGninthN4pXHT19Nums, 2048),
    (wGninthN4pXHT20Labs, wGninthN4pXHT20Nums, 2048), (wGninthN4pXHT21Labs, wGninthN4pXHT21Nums,
    2048), (wGninthN4pXHT22Labs, wGninthN4pXHT22Nums, 2048), (wGninthN4pXHT23Labs,
    wGninthN4pXHT23Nums, 2048), (wGninthN4pXHT24Labs, wGninthN4pXHT24Nums, 2048),
    (wGninthN4pXHT25Labs, wGninthN4pXHT25Nums, 2048), (wGninthN4pXHT26Labs, wGninthN4pXHT26Nums,
    2048), (wGninthN4pXHT27Labs, wGninthN4pXHT27Nums, 2048), (wGninthN4pXHT28Labs,
    wGninthN4pXHT28Nums, 2048), (wGninthN4pXHT29Labs, wGninthN4pXHT29Nums, 2048),
    (wGninthN4pXHT30Labs, wGninthN4pXHT30Nums, 144)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

set_option maxRecDepth 100000 in
/-- The dense odd tensor part of the source (gident's `OddDense`, one pass over the source
chunks). -/
theorem wGninthN4pX_nlchk : OddDense.oddChk 64 ((2 ^ 4 - 1) * 2 ^ 0) false true
    [(wGninthN4pXHT0Labs, wGninthN4pXHT0Nums, 2048), (wGninthN4pXHT1Labs, wGninthN4pXHT1Nums,
    2048), (wGninthN4pXHT2Labs, wGninthN4pXHT2Nums, 2048), (wGninthN4pXHT3Labs,
    wGninthN4pXHT3Nums, 2048), (wGninthN4pXHT4Labs, wGninthN4pXHT4Nums, 2048),
    (wGninthN4pXHT5Labs, wGninthN4pXHT5Nums, 2048), (wGninthN4pXHT6Labs, wGninthN4pXHT6Nums,
    2048), (wGninthN4pXHT7Labs, wGninthN4pXHT7Nums, 2048), (wGninthN4pXHT8Labs,
    wGninthN4pXHT8Nums, 2048), (wGninthN4pXHT9Labs, wGninthN4pXHT9Nums, 2048),
    (wGninthN4pXHT10Labs, wGninthN4pXHT10Nums, 2048), (wGninthN4pXHT11Labs, wGninthN4pXHT11Nums,
    2048), (wGninthN4pXHT12Labs, wGninthN4pXHT12Nums, 2048), (wGninthN4pXHT13Labs,
    wGninthN4pXHT13Nums, 2048), (wGninthN4pXHT14Labs, wGninthN4pXHT14Nums, 2048),
    (wGninthN4pXHT15Labs, wGninthN4pXHT15Nums, 2048), (wGninthN4pXHT16Labs, wGninthN4pXHT16Nums,
    2048), (wGninthN4pXHT17Labs, wGninthN4pXHT17Nums, 2048), (wGninthN4pXHT18Labs,
    wGninthN4pXHT18Nums, 2048), (wGninthN4pXHT19Labs, wGninthN4pXHT19Nums, 2048),
    (wGninthN4pXHT20Labs, wGninthN4pXHT20Nums, 2048), (wGninthN4pXHT21Labs, wGninthN4pXHT21Nums,
    2048), (wGninthN4pXHT22Labs, wGninthN4pXHT22Nums, 2048), (wGninthN4pXHT23Labs,
    wGninthN4pXHT23Nums, 2048), (wGninthN4pXHT24Labs, wGninthN4pXHT24Nums, 2048),
    (wGninthN4pXHT25Labs, wGninthN4pXHT25Nums, 2048), (wGninthN4pXHT26Labs, wGninthN4pXHT26Nums,
    2048), (wGninthN4pXHT27Labs, wGninthN4pXHT27Nums, 2048), (wGninthN4pXHT28Labs,
    wGninthN4pXHT28Nums, 2048), (wGninthN4pXHT29Labs, wGninthN4pXHT29Nums, 2048),
    (wGninthN4pXHT30Labs, wGninthN4pXHT30Nums, 144)] wGninthN4pXGX0 (256000) = true := by
  decide +kernel

/-- The odd tensor part of the source. -/
theorem wGninthN4pX_nl : oddLZ 64 true wGninthN4pXGX0 wGninthN4pXL = 256000 :=
  OddDense.oddLZ_of_chk true wGninthN4pXL wGninthN4pXW _ wGninthN4pX_LshC (wGninthN4pXGX0_ten
      ((tensorWordDenAll wGninthN4pXG : ℚ) * 32)).symm (by decide +kernel)
    (by decide +kernel) wGninthN4pXGX0_bnd wGninthN4pX_nlchk

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem wGninthN4pX_v1 : tdotM 64 (trialityTensorT 64 (!true) wGninthN4pXHX0) wGninthN4pXGX0 =
    129024 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor self dot of the target. -/
theorem wGninthN4pX_v2 : tdotM 64 wGninthN4pXGX0 wGninthN4pXGX0 = 128512 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wGninthN4pX_ht : wGninthN4pXL.sden * (oddLZ 64 true wGninthN4pXGX0 wGninthN4pXL : ℚ) /
    (((tensorWordDenAll wGninthN4pXG : ℚ) * 32) / 2 ^ 9) +
    (tdotM 64 (trialityTensorT 64 (!true) wGninthN4pXHX0) wGninthN4pXGX0 : ℚ) / (2 *
        (((tensorWordDenAll wGninthN4pXH : ℚ) * 32) / 2 ^ 4) * (((tensorWordDenAll wGninthN4pXG :
        ℚ) * 32) / 2 ^ 9)) =
      (tdotM 64 wGninthN4pXGX0 wGninthN4pXGX0 : ℚ) / ((((tensorWordDenAll wGninthN4pXG : ℚ) * 32)
          / 2 ^ 9) * (((tensorWordDenAll wGninthN4pXG : ℚ) * 32) / 2 ^ 9)) := by
  rw [wGninthN4pX_nl, wGninthN4pX_v1, wGninthN4pX_v2]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
