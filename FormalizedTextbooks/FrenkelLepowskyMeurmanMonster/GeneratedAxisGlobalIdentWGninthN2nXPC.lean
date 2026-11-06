/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN2nXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN2nXTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (tensor) of the identification Ninth[3]- <-> Tenth[50]+ (record gninth:N2-, e
= -1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The source short block as packed chunks. -/
theorem wGninthN2nX_LshC : wGninthN2nXL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN2nXHT0Labs, wGninthN2nXHT0Nums, 2048), (wGninthN2nXHT1Labs, wGninthN2nXHT1Nums,
    2048), (wGninthN2nXHT2Labs, wGninthN2nXHT2Nums, 2048), (wGninthN2nXHT3Labs,
    wGninthN2nXHT3Nums, 2048), (wGninthN2nXHT4Labs, wGninthN2nXHT4Nums, 2048),
    (wGninthN2nXHT5Labs, wGninthN2nXHT5Nums, 2048), (wGninthN2nXHT6Labs, wGninthN2nXHT6Nums,
    2048), (wGninthN2nXHT7Labs, wGninthN2nXHT7Nums, 2048), (wGninthN2nXHT8Labs,
    wGninthN2nXHT8Nums, 2048), (wGninthN2nXHT9Labs, wGninthN2nXHT9Nums, 2048),
    (wGninthN2nXHT10Labs, wGninthN2nXHT10Nums, 2048), (wGninthN2nXHT11Labs, wGninthN2nXHT11Nums,
    2048), (wGninthN2nXHT12Labs, wGninthN2nXHT12Nums, 2048), (wGninthN2nXHT13Labs,
    wGninthN2nXHT13Nums, 2048), (wGninthN2nXHT14Labs, wGninthN2nXHT14Nums, 2048),
    (wGninthN2nXHT15Labs, wGninthN2nXHT15Nums, 2048), (wGninthN2nXHT16Labs, wGninthN2nXHT16Nums,
    2048), (wGninthN2nXHT17Labs, wGninthN2nXHT17Nums, 2048), (wGninthN2nXHT18Labs,
    wGninthN2nXHT18Nums, 2048), (wGninthN2nXHT19Labs, wGninthN2nXHT19Nums, 2048),
    (wGninthN2nXHT20Labs, wGninthN2nXHT20Nums, 2048), (wGninthN2nXHT21Labs, wGninthN2nXHT21Nums,
    2048), (wGninthN2nXHT22Labs, wGninthN2nXHT22Nums, 2048), (wGninthN2nXHT23Labs,
    wGninthN2nXHT23Nums, 2048), (wGninthN2nXHT24Labs, wGninthN2nXHT24Nums, 2048),
    (wGninthN2nXHT25Labs, wGninthN2nXHT25Nums, 2048), (wGninthN2nXHT26Labs, wGninthN2nXHT26Nums,
    2048), (wGninthN2nXHT27Labs, wGninthN2nXHT27Nums, 2048), (wGninthN2nXHT28Labs,
    wGninthN2nXHT28Nums, 2048), (wGninthN2nXHT29Labs, wGninthN2nXHT29Nums, 2048),
    (wGninthN2nXHT30Labs, wGninthN2nXHT30Nums, 144)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

set_option maxRecDepth 100000 in
/-- The dense odd tensor part of the source (gident's `OddDense`, one pass over the source
chunks). -/
theorem wGninthN2nX_nlchk : OddDense.oddChk 64 ((2 ^ 4 - 1) * 2 ^ 0) true false
    [(wGninthN2nXHT0Labs, wGninthN2nXHT0Nums, 2048), (wGninthN2nXHT1Labs, wGninthN2nXHT1Nums,
    2048), (wGninthN2nXHT2Labs, wGninthN2nXHT2Nums, 2048), (wGninthN2nXHT3Labs,
    wGninthN2nXHT3Nums, 2048), (wGninthN2nXHT4Labs, wGninthN2nXHT4Nums, 2048),
    (wGninthN2nXHT5Labs, wGninthN2nXHT5Nums, 2048), (wGninthN2nXHT6Labs, wGninthN2nXHT6Nums,
    2048), (wGninthN2nXHT7Labs, wGninthN2nXHT7Nums, 2048), (wGninthN2nXHT8Labs,
    wGninthN2nXHT8Nums, 2048), (wGninthN2nXHT9Labs, wGninthN2nXHT9Nums, 2048),
    (wGninthN2nXHT10Labs, wGninthN2nXHT10Nums, 2048), (wGninthN2nXHT11Labs, wGninthN2nXHT11Nums,
    2048), (wGninthN2nXHT12Labs, wGninthN2nXHT12Nums, 2048), (wGninthN2nXHT13Labs,
    wGninthN2nXHT13Nums, 2048), (wGninthN2nXHT14Labs, wGninthN2nXHT14Nums, 2048),
    (wGninthN2nXHT15Labs, wGninthN2nXHT15Nums, 2048), (wGninthN2nXHT16Labs, wGninthN2nXHT16Nums,
    2048), (wGninthN2nXHT17Labs, wGninthN2nXHT17Nums, 2048), (wGninthN2nXHT18Labs,
    wGninthN2nXHT18Nums, 2048), (wGninthN2nXHT19Labs, wGninthN2nXHT19Nums, 2048),
    (wGninthN2nXHT20Labs, wGninthN2nXHT20Nums, 2048), (wGninthN2nXHT21Labs, wGninthN2nXHT21Nums,
    2048), (wGninthN2nXHT22Labs, wGninthN2nXHT22Nums, 2048), (wGninthN2nXHT23Labs,
    wGninthN2nXHT23Nums, 2048), (wGninthN2nXHT24Labs, wGninthN2nXHT24Nums, 2048),
    (wGninthN2nXHT25Labs, wGninthN2nXHT25Nums, 2048), (wGninthN2nXHT26Labs, wGninthN2nXHT26Nums,
    2048), (wGninthN2nXHT27Labs, wGninthN2nXHT27Nums, 2048), (wGninthN2nXHT28Labs,
    wGninthN2nXHT28Nums, 2048), (wGninthN2nXHT29Labs, wGninthN2nXHT29Nums, 2048),
    (wGninthN2nXHT30Labs, wGninthN2nXHT30Nums, 144)] wGninthN2nXGX0 (256000) = true := by
  decide +kernel

/-- The odd tensor part of the source. -/
theorem wGninthN2nX_nl : oddLZ 64 false wGninthN2nXGX0 wGninthN2nXL = 256000 :=
  OddDense.oddLZ_of_chk false wGninthN2nXL wGninthN2nXW _ wGninthN2nX_LshC (wGninthN2nXGX0_ten
      ((tensorWordDenAll wGninthN2nXG : ℚ) * 32)).symm (by decide +kernel)
    (by decide +kernel) wGninthN2nXGX0_bnd wGninthN2nX_nlchk

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem wGninthN2nX_v1 : tdotM 64 (trialityTensorT 64 (!false) wGninthN2nXHX0) wGninthN2nXGX0 =
    129024 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor self dot of the target. -/
theorem wGninthN2nX_v2 : tdotM 64 wGninthN2nXGX0 wGninthN2nXGX0 = 128512 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wGninthN2nX_ht : wGninthN2nXL.sden * (oddLZ 64 false wGninthN2nXGX0 wGninthN2nXL : ℚ) /
    (((tensorWordDenAll wGninthN2nXG : ℚ) * 32) / 2 ^ 25) +
    (tdotM 64 (trialityTensorT 64 (!false) wGninthN2nXHX0) wGninthN2nXGX0 : ℚ) / (2 *
        (((tensorWordDenAll wGninthN2nXH : ℚ) * 32) / 2 ^ 8) * (((tensorWordDenAll wGninthN2nXG :
        ℚ) * 32) / 2 ^ 25)) =
      (tdotM 64 wGninthN2nXGX0 wGninthN2nXGX0 : ℚ) / ((((tensorWordDenAll wGninthN2nXG : ℚ) * 32)
          / 2 ^ 25) * (((tensorWordDenAll wGninthN2nXG : ℚ) * 32) / 2 ^ 25)) := by
  rw [wGninthN2nX_nl, wGninthN2nX_v1, wGninthN2nX_v2]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
