/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN6nXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN6nXTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (tensor) of the identification Ninth[10]- <-> Twelfth[12]- (record gninth:N6-,
e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The source short block as packed chunks. -/
theorem wGninthN6nX_LshC : wGninthN6nXL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN6nXHT0Labs, wGninthN6nXHT0Nums, 2048), (wGninthN6nXHT1Labs, wGninthN6nXHT1Nums,
    2048), (wGninthN6nXHT2Labs, wGninthN6nXHT2Nums, 2048), (wGninthN6nXHT3Labs,
    wGninthN6nXHT3Nums, 2048), (wGninthN6nXHT4Labs, wGninthN6nXHT4Nums, 2048),
    (wGninthN6nXHT5Labs, wGninthN6nXHT5Nums, 2048), (wGninthN6nXHT6Labs, wGninthN6nXHT6Nums,
    2048), (wGninthN6nXHT7Labs, wGninthN6nXHT7Nums, 2048), (wGninthN6nXHT8Labs,
    wGninthN6nXHT8Nums, 2048), (wGninthN6nXHT9Labs, wGninthN6nXHT9Nums, 2048),
    (wGninthN6nXHT10Labs, wGninthN6nXHT10Nums, 2048), (wGninthN6nXHT11Labs, wGninthN6nXHT11Nums,
    2048), (wGninthN6nXHT12Labs, wGninthN6nXHT12Nums, 2048), (wGninthN6nXHT13Labs,
    wGninthN6nXHT13Nums, 2048), (wGninthN6nXHT14Labs, wGninthN6nXHT14Nums, 2048),
    (wGninthN6nXHT15Labs, wGninthN6nXHT15Nums, 2048), (wGninthN6nXHT16Labs, wGninthN6nXHT16Nums,
    2048), (wGninthN6nXHT17Labs, wGninthN6nXHT17Nums, 2048), (wGninthN6nXHT18Labs,
    wGninthN6nXHT18Nums, 2048), (wGninthN6nXHT19Labs, wGninthN6nXHT19Nums, 2048),
    (wGninthN6nXHT20Labs, wGninthN6nXHT20Nums, 2048), (wGninthN6nXHT21Labs, wGninthN6nXHT21Nums,
    2048), (wGninthN6nXHT22Labs, wGninthN6nXHT22Nums, 2048), (wGninthN6nXHT23Labs,
    wGninthN6nXHT23Nums, 2048), (wGninthN6nXHT24Labs, wGninthN6nXHT24Nums, 2048),
    (wGninthN6nXHT25Labs, wGninthN6nXHT25Nums, 2048), (wGninthN6nXHT26Labs, wGninthN6nXHT26Nums,
    2048), (wGninthN6nXHT27Labs, wGninthN6nXHT27Nums, 2048), (wGninthN6nXHT28Labs,
    wGninthN6nXHT28Nums, 2048), (wGninthN6nXHT29Labs, wGninthN6nXHT29Nums, 2048),
    (wGninthN6nXHT30Labs, wGninthN6nXHT30Nums, 144)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

set_option maxRecDepth 100000 in
/-- The dense odd tensor part of the source (gident's `OddDense`, one pass over the source
chunks). -/
theorem wGninthN6nX_nlchk : OddDense.oddChk 64 ((2 ^ 3 - 1) * 2 ^ 0) true false
    [(wGninthN6nXHT0Labs, wGninthN6nXHT0Nums, 2048), (wGninthN6nXHT1Labs, wGninthN6nXHT1Nums,
    2048), (wGninthN6nXHT2Labs, wGninthN6nXHT2Nums, 2048), (wGninthN6nXHT3Labs,
    wGninthN6nXHT3Nums, 2048), (wGninthN6nXHT4Labs, wGninthN6nXHT4Nums, 2048),
    (wGninthN6nXHT5Labs, wGninthN6nXHT5Nums, 2048), (wGninthN6nXHT6Labs, wGninthN6nXHT6Nums,
    2048), (wGninthN6nXHT7Labs, wGninthN6nXHT7Nums, 2048), (wGninthN6nXHT8Labs,
    wGninthN6nXHT8Nums, 2048), (wGninthN6nXHT9Labs, wGninthN6nXHT9Nums, 2048),
    (wGninthN6nXHT10Labs, wGninthN6nXHT10Nums, 2048), (wGninthN6nXHT11Labs, wGninthN6nXHT11Nums,
    2048), (wGninthN6nXHT12Labs, wGninthN6nXHT12Nums, 2048), (wGninthN6nXHT13Labs,
    wGninthN6nXHT13Nums, 2048), (wGninthN6nXHT14Labs, wGninthN6nXHT14Nums, 2048),
    (wGninthN6nXHT15Labs, wGninthN6nXHT15Nums, 2048), (wGninthN6nXHT16Labs, wGninthN6nXHT16Nums,
    2048), (wGninthN6nXHT17Labs, wGninthN6nXHT17Nums, 2048), (wGninthN6nXHT18Labs,
    wGninthN6nXHT18Nums, 2048), (wGninthN6nXHT19Labs, wGninthN6nXHT19Nums, 2048),
    (wGninthN6nXHT20Labs, wGninthN6nXHT20Nums, 2048), (wGninthN6nXHT21Labs, wGninthN6nXHT21Nums,
    2048), (wGninthN6nXHT22Labs, wGninthN6nXHT22Nums, 2048), (wGninthN6nXHT23Labs,
    wGninthN6nXHT23Nums, 2048), (wGninthN6nXHT24Labs, wGninthN6nXHT24Nums, 2048),
    (wGninthN6nXHT25Labs, wGninthN6nXHT25Nums, 2048), (wGninthN6nXHT26Labs, wGninthN6nXHT26Nums,
    2048), (wGninthN6nXHT27Labs, wGninthN6nXHT27Nums, 2048), (wGninthN6nXHT28Labs,
    wGninthN6nXHT28Nums, 2048), (wGninthN6nXHT29Labs, wGninthN6nXHT29Nums, 2048),
    (wGninthN6nXHT30Labs, wGninthN6nXHT30Nums, 144)] wGninthN6nXGX0 (253952) = true := by
  decide +kernel

/-- The odd tensor part of the source. -/
theorem wGninthN6nX_nl : oddLZ 64 false wGninthN6nXGX0 wGninthN6nXL = 253952 :=
  OddDense.oddLZ_of_chk false wGninthN6nXL wGninthN6nXW _ wGninthN6nX_LshC (wGninthN6nXGX0_ten
      ((tensorWordDenAll wGninthN6nXG : ℚ) * 32)).symm (by decide +kernel)
    (by decide +kernel) wGninthN6nXGX0_bnd wGninthN6nX_nlchk

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem wGninthN6nX_v1 : tdotM 64 (trialityTensorT 64 (!false) wGninthN6nXHX0) wGninthN6nXGX0 =
    129024 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor self dot of the target. -/
theorem wGninthN6nX_v2 : tdotM 64 wGninthN6nXGX0 wGninthN6nXGX0 = 128000 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wGninthN6nX_ht : wGninthN6nXL.sden * (oddLZ 64 false wGninthN6nXGX0 wGninthN6nXL : ℚ) /
    (((tensorWordDenAll wGninthN6nXG : ℚ) * 32) / 2 ^ 9) +
    (tdotM 64 (trialityTensorT 64 (!false) wGninthN6nXHX0) wGninthN6nXGX0 : ℚ) / (2 *
        (((tensorWordDenAll wGninthN6nXH : ℚ) * 32) / 2 ^ 16) * (((tensorWordDenAll wGninthN6nXG :
        ℚ) * 32) / 2 ^ 9)) =
      (tdotM 64 wGninthN6nXGX0 wGninthN6nXGX0 : ℚ) / ((((tensorWordDenAll wGninthN6nXG : ℚ) * 32)
          / 2 ^ 9) * (((tensorWordDenAll wGninthN6nXG : ℚ) * 32) / 2 ^ 9)) := by
  rw [wGninthN6nX_nl, wGninthN6nX_v1, wGninthN6nX_v2]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
