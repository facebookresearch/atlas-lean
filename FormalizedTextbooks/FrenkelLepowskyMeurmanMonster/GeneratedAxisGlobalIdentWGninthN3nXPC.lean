/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN3nXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN3nXTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (tensor) of the identification Ninth[5]- <-> Twelfth[31]+ (record gninth:N3-,
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
theorem wGninthN3nX_LshC : wGninthN3nXL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN3nXHT0Labs, wGninthN3nXHT0Nums, 2048), (wGninthN3nXHT1Labs, wGninthN3nXHT1Nums,
    2048), (wGninthN3nXHT2Labs, wGninthN3nXHT2Nums, 2048), (wGninthN3nXHT3Labs,
    wGninthN3nXHT3Nums, 2048), (wGninthN3nXHT4Labs, wGninthN3nXHT4Nums, 2048),
    (wGninthN3nXHT5Labs, wGninthN3nXHT5Nums, 2048), (wGninthN3nXHT6Labs, wGninthN3nXHT6Nums,
    2048), (wGninthN3nXHT7Labs, wGninthN3nXHT7Nums, 2048), (wGninthN3nXHT8Labs,
    wGninthN3nXHT8Nums, 2048), (wGninthN3nXHT9Labs, wGninthN3nXHT9Nums, 2048),
    (wGninthN3nXHT10Labs, wGninthN3nXHT10Nums, 2048), (wGninthN3nXHT11Labs, wGninthN3nXHT11Nums,
    2048), (wGninthN3nXHT12Labs, wGninthN3nXHT12Nums, 2048), (wGninthN3nXHT13Labs,
    wGninthN3nXHT13Nums, 2048), (wGninthN3nXHT14Labs, wGninthN3nXHT14Nums, 2048),
    (wGninthN3nXHT15Labs, wGninthN3nXHT15Nums, 2048), (wGninthN3nXHT16Labs, wGninthN3nXHT16Nums,
    2048), (wGninthN3nXHT17Labs, wGninthN3nXHT17Nums, 2048), (wGninthN3nXHT18Labs,
    wGninthN3nXHT18Nums, 2048), (wGninthN3nXHT19Labs, wGninthN3nXHT19Nums, 2048),
    (wGninthN3nXHT20Labs, wGninthN3nXHT20Nums, 2048), (wGninthN3nXHT21Labs, wGninthN3nXHT21Nums,
    2048), (wGninthN3nXHT22Labs, wGninthN3nXHT22Nums, 2048), (wGninthN3nXHT23Labs,
    wGninthN3nXHT23Nums, 2048), (wGninthN3nXHT24Labs, wGninthN3nXHT24Nums, 2048),
    (wGninthN3nXHT25Labs, wGninthN3nXHT25Nums, 2048), (wGninthN3nXHT26Labs, wGninthN3nXHT26Nums,
    2048), (wGninthN3nXHT27Labs, wGninthN3nXHT27Nums, 2048), (wGninthN3nXHT28Labs,
    wGninthN3nXHT28Nums, 2048), (wGninthN3nXHT29Labs, wGninthN3nXHT29Nums, 2048),
    (wGninthN3nXHT30Labs, wGninthN3nXHT30Nums, 144)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

set_option maxRecDepth 100000 in
/-- The dense odd tensor part of the source (gident's `OddDense`, one pass over the source
chunks). -/
theorem wGninthN3nX_nlchk : OddDense.oddChk 64 ((2 ^ 3 - 1) * 2 ^ 0) true false
    [(wGninthN3nXHT0Labs, wGninthN3nXHT0Nums, 2048), (wGninthN3nXHT1Labs, wGninthN3nXHT1Nums,
    2048), (wGninthN3nXHT2Labs, wGninthN3nXHT2Nums, 2048), (wGninthN3nXHT3Labs,
    wGninthN3nXHT3Nums, 2048), (wGninthN3nXHT4Labs, wGninthN3nXHT4Nums, 2048),
    (wGninthN3nXHT5Labs, wGninthN3nXHT5Nums, 2048), (wGninthN3nXHT6Labs, wGninthN3nXHT6Nums,
    2048), (wGninthN3nXHT7Labs, wGninthN3nXHT7Nums, 2048), (wGninthN3nXHT8Labs,
    wGninthN3nXHT8Nums, 2048), (wGninthN3nXHT9Labs, wGninthN3nXHT9Nums, 2048),
    (wGninthN3nXHT10Labs, wGninthN3nXHT10Nums, 2048), (wGninthN3nXHT11Labs, wGninthN3nXHT11Nums,
    2048), (wGninthN3nXHT12Labs, wGninthN3nXHT12Nums, 2048), (wGninthN3nXHT13Labs,
    wGninthN3nXHT13Nums, 2048), (wGninthN3nXHT14Labs, wGninthN3nXHT14Nums, 2048),
    (wGninthN3nXHT15Labs, wGninthN3nXHT15Nums, 2048), (wGninthN3nXHT16Labs, wGninthN3nXHT16Nums,
    2048), (wGninthN3nXHT17Labs, wGninthN3nXHT17Nums, 2048), (wGninthN3nXHT18Labs,
    wGninthN3nXHT18Nums, 2048), (wGninthN3nXHT19Labs, wGninthN3nXHT19Nums, 2048),
    (wGninthN3nXHT20Labs, wGninthN3nXHT20Nums, 2048), (wGninthN3nXHT21Labs, wGninthN3nXHT21Nums,
    2048), (wGninthN3nXHT22Labs, wGninthN3nXHT22Nums, 2048), (wGninthN3nXHT23Labs,
    wGninthN3nXHT23Nums, 2048), (wGninthN3nXHT24Labs, wGninthN3nXHT24Nums, 2048),
    (wGninthN3nXHT25Labs, wGninthN3nXHT25Nums, 2048), (wGninthN3nXHT26Labs, wGninthN3nXHT26Nums,
    2048), (wGninthN3nXHT27Labs, wGninthN3nXHT27Nums, 2048), (wGninthN3nXHT28Labs,
    wGninthN3nXHT28Nums, 2048), (wGninthN3nXHT29Labs, wGninthN3nXHT29Nums, 2048),
    (wGninthN3nXHT30Labs, wGninthN3nXHT30Nums, 144)] wGninthN3nXGX0 (253952) = true := by
  decide +kernel

/-- The odd tensor part of the source. -/
theorem wGninthN3nX_nl : oddLZ 64 false wGninthN3nXGX0 wGninthN3nXL = 253952 :=
  OddDense.oddLZ_of_chk false wGninthN3nXL wGninthN3nXW _ wGninthN3nX_LshC (wGninthN3nXGX0_ten
      ((tensorWordDenAll wGninthN3nXG : ℚ) * 32)).symm (by decide +kernel)
    (by decide +kernel) wGninthN3nXGX0_bnd wGninthN3nX_nlchk

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem wGninthN3nX_v1 : tdotM 64 (trialityTensorT 64 (!false) wGninthN3nXHX0) wGninthN3nXGX0 =
    129024 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor self dot of the target. -/
theorem wGninthN3nX_v2 : tdotM 64 wGninthN3nXGX0 wGninthN3nXGX0 = 128000 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wGninthN3nX_ht : wGninthN3nXL.sden * (oddLZ 64 false wGninthN3nXGX0 wGninthN3nXL : ℚ) /
    (((tensorWordDenAll wGninthN3nXG : ℚ) * 32) / 2 ^ 9) +
    (tdotM 64 (trialityTensorT 64 (!false) wGninthN3nXHX0) wGninthN3nXGX0 : ℚ) / (2 *
        (((tensorWordDenAll wGninthN3nXH : ℚ) * 32) / 2 ^ 4) * (((tensorWordDenAll wGninthN3nXG :
        ℚ) * 32) / 2 ^ 9)) =
      (tdotM 64 wGninthN3nXGX0 wGninthN3nXGX0 : ℚ) / ((((tensorWordDenAll wGninthN3nXG : ℚ) * 32)
          / 2 ^ 9) * (((tensorWordDenAll wGninthN3nXG : ℚ) * 32) / 2 ^ 9)) := by
  rw [wGninthN3nX_nl, wGninthN3nX_v1, wGninthN3nX_v2]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
