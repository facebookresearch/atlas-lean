/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN4nXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN4nXTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (tensor) of the identification Ninth[6]- <-> Tenth[74]- (record gninth:N4-, e
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
theorem wGninthN4nX_LshC : wGninthN4nXL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN4nXHT0Labs, wGninthN4nXHT0Nums, 2048), (wGninthN4nXHT1Labs, wGninthN4nXHT1Nums,
    2048), (wGninthN4nXHT2Labs, wGninthN4nXHT2Nums, 2048), (wGninthN4nXHT3Labs,
    wGninthN4nXHT3Nums, 2048), (wGninthN4nXHT4Labs, wGninthN4nXHT4Nums, 2048),
    (wGninthN4nXHT5Labs, wGninthN4nXHT5Nums, 2048), (wGninthN4nXHT6Labs, wGninthN4nXHT6Nums,
    2048), (wGninthN4nXHT7Labs, wGninthN4nXHT7Nums, 2048), (wGninthN4nXHT8Labs,
    wGninthN4nXHT8Nums, 2048), (wGninthN4nXHT9Labs, wGninthN4nXHT9Nums, 2048),
    (wGninthN4nXHT10Labs, wGninthN4nXHT10Nums, 2048), (wGninthN4nXHT11Labs, wGninthN4nXHT11Nums,
    2048), (wGninthN4nXHT12Labs, wGninthN4nXHT12Nums, 2048), (wGninthN4nXHT13Labs,
    wGninthN4nXHT13Nums, 2048), (wGninthN4nXHT14Labs, wGninthN4nXHT14Nums, 2048),
    (wGninthN4nXHT15Labs, wGninthN4nXHT15Nums, 2048), (wGninthN4nXHT16Labs, wGninthN4nXHT16Nums,
    2048), (wGninthN4nXHT17Labs, wGninthN4nXHT17Nums, 2048), (wGninthN4nXHT18Labs,
    wGninthN4nXHT18Nums, 2048), (wGninthN4nXHT19Labs, wGninthN4nXHT19Nums, 2048),
    (wGninthN4nXHT20Labs, wGninthN4nXHT20Nums, 2048), (wGninthN4nXHT21Labs, wGninthN4nXHT21Nums,
    2048), (wGninthN4nXHT22Labs, wGninthN4nXHT22Nums, 2048), (wGninthN4nXHT23Labs,
    wGninthN4nXHT23Nums, 2048), (wGninthN4nXHT24Labs, wGninthN4nXHT24Nums, 2048),
    (wGninthN4nXHT25Labs, wGninthN4nXHT25Nums, 2048), (wGninthN4nXHT26Labs, wGninthN4nXHT26Nums,
    2048), (wGninthN4nXHT27Labs, wGninthN4nXHT27Nums, 2048), (wGninthN4nXHT28Labs,
    wGninthN4nXHT28Nums, 2048), (wGninthN4nXHT29Labs, wGninthN4nXHT29Nums, 2048),
    (wGninthN4nXHT30Labs, wGninthN4nXHT30Nums, 144)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

set_option maxRecDepth 100000 in
/-- The dense odd tensor part of the source (gident's `OddDense`, one pass over the source
chunks). -/
theorem wGninthN4nX_nlchk : OddDense.oddChk 64 ((2 ^ 4 - 1) * 2 ^ 0) true false
    [(wGninthN4nXHT0Labs, wGninthN4nXHT0Nums, 2048), (wGninthN4nXHT1Labs, wGninthN4nXHT1Nums,
    2048), (wGninthN4nXHT2Labs, wGninthN4nXHT2Nums, 2048), (wGninthN4nXHT3Labs,
    wGninthN4nXHT3Nums, 2048), (wGninthN4nXHT4Labs, wGninthN4nXHT4Nums, 2048),
    (wGninthN4nXHT5Labs, wGninthN4nXHT5Nums, 2048), (wGninthN4nXHT6Labs, wGninthN4nXHT6Nums,
    2048), (wGninthN4nXHT7Labs, wGninthN4nXHT7Nums, 2048), (wGninthN4nXHT8Labs,
    wGninthN4nXHT8Nums, 2048), (wGninthN4nXHT9Labs, wGninthN4nXHT9Nums, 2048),
    (wGninthN4nXHT10Labs, wGninthN4nXHT10Nums, 2048), (wGninthN4nXHT11Labs, wGninthN4nXHT11Nums,
    2048), (wGninthN4nXHT12Labs, wGninthN4nXHT12Nums, 2048), (wGninthN4nXHT13Labs,
    wGninthN4nXHT13Nums, 2048), (wGninthN4nXHT14Labs, wGninthN4nXHT14Nums, 2048),
    (wGninthN4nXHT15Labs, wGninthN4nXHT15Nums, 2048), (wGninthN4nXHT16Labs, wGninthN4nXHT16Nums,
    2048), (wGninthN4nXHT17Labs, wGninthN4nXHT17Nums, 2048), (wGninthN4nXHT18Labs,
    wGninthN4nXHT18Nums, 2048), (wGninthN4nXHT19Labs, wGninthN4nXHT19Nums, 2048),
    (wGninthN4nXHT20Labs, wGninthN4nXHT20Nums, 2048), (wGninthN4nXHT21Labs, wGninthN4nXHT21Nums,
    2048), (wGninthN4nXHT22Labs, wGninthN4nXHT22Nums, 2048), (wGninthN4nXHT23Labs,
    wGninthN4nXHT23Nums, 2048), (wGninthN4nXHT24Labs, wGninthN4nXHT24Nums, 2048),
    (wGninthN4nXHT25Labs, wGninthN4nXHT25Nums, 2048), (wGninthN4nXHT26Labs, wGninthN4nXHT26Nums,
    2048), (wGninthN4nXHT27Labs, wGninthN4nXHT27Nums, 2048), (wGninthN4nXHT28Labs,
    wGninthN4nXHT28Nums, 2048), (wGninthN4nXHT29Labs, wGninthN4nXHT29Nums, 2048),
    (wGninthN4nXHT30Labs, wGninthN4nXHT30Nums, 144)] wGninthN4nXGX0 (256000) = true := by
  decide +kernel

/-- The odd tensor part of the source. -/
theorem wGninthN4nX_nl : oddLZ 64 false wGninthN4nXGX0 wGninthN4nXL = 256000 :=
  OddDense.oddLZ_of_chk false wGninthN4nXL wGninthN4nXW _ wGninthN4nX_LshC (wGninthN4nXGX0_ten
      ((tensorWordDenAll wGninthN4nXG : ℚ) * 32)).symm (by decide +kernel)
    (by decide +kernel) wGninthN4nXGX0_bnd wGninthN4nX_nlchk

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem wGninthN4nX_v1 : tdotM 64 (trialityTensorT 64 (!false) wGninthN4nXHX0) wGninthN4nXGX0 =
    129024 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor self dot of the target. -/
theorem wGninthN4nX_v2 : tdotM 64 wGninthN4nXGX0 wGninthN4nXGX0 = 128512 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wGninthN4nX_ht : wGninthN4nXL.sden * (oddLZ 64 false wGninthN4nXGX0 wGninthN4nXL : ℚ) /
    (((tensorWordDenAll wGninthN4nXG : ℚ) * 32) / 2 ^ 9) +
    (tdotM 64 (trialityTensorT 64 (!false) wGninthN4nXHX0) wGninthN4nXGX0 : ℚ) / (2 *
        (((tensorWordDenAll wGninthN4nXH : ℚ) * 32) / 2 ^ 4) * (((tensorWordDenAll wGninthN4nXG :
        ℚ) * 32) / 2 ^ 9)) =
      (tdotM 64 wGninthN4nXGX0 wGninthN4nXGX0 : ℚ) / ((((tensorWordDenAll wGninthN4nXG : ℚ) * 32)
          / 2 ^ 9) * (((tensorWordDenAll wGninthN4nXG : ℚ) * 32) / 2 ^ 9)) := by
  rw [wGninthN4nX_nl, wGninthN4nX_v1, wGninthN4nX_v2]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
