/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN3pXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN3pXTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (tensor) of the identification Ninth[5]+ <-> Twelfth[31]+ (record gninth:N3+,
e = 1)

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
theorem wGninthN3pX_LshC : wGninthN3pXL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN3pXHT0Labs, wGninthN3pXHT0Nums, 2048), (wGninthN3pXHT1Labs, wGninthN3pXHT1Nums,
    2048), (wGninthN3pXHT2Labs, wGninthN3pXHT2Nums, 2048), (wGninthN3pXHT3Labs,
    wGninthN3pXHT3Nums, 2048), (wGninthN3pXHT4Labs, wGninthN3pXHT4Nums, 2048),
    (wGninthN3pXHT5Labs, wGninthN3pXHT5Nums, 2048), (wGninthN3pXHT6Labs, wGninthN3pXHT6Nums,
    2048), (wGninthN3pXHT7Labs, wGninthN3pXHT7Nums, 2048), (wGninthN3pXHT8Labs,
    wGninthN3pXHT8Nums, 2048), (wGninthN3pXHT9Labs, wGninthN3pXHT9Nums, 2048),
    (wGninthN3pXHT10Labs, wGninthN3pXHT10Nums, 2048), (wGninthN3pXHT11Labs, wGninthN3pXHT11Nums,
    2048), (wGninthN3pXHT12Labs, wGninthN3pXHT12Nums, 2048), (wGninthN3pXHT13Labs,
    wGninthN3pXHT13Nums, 2048), (wGninthN3pXHT14Labs, wGninthN3pXHT14Nums, 2048),
    (wGninthN3pXHT15Labs, wGninthN3pXHT15Nums, 2048), (wGninthN3pXHT16Labs, wGninthN3pXHT16Nums,
    2048), (wGninthN3pXHT17Labs, wGninthN3pXHT17Nums, 2048), (wGninthN3pXHT18Labs,
    wGninthN3pXHT18Nums, 2048), (wGninthN3pXHT19Labs, wGninthN3pXHT19Nums, 2048),
    (wGninthN3pXHT20Labs, wGninthN3pXHT20Nums, 2048), (wGninthN3pXHT21Labs, wGninthN3pXHT21Nums,
    2048), (wGninthN3pXHT22Labs, wGninthN3pXHT22Nums, 2048), (wGninthN3pXHT23Labs,
    wGninthN3pXHT23Nums, 2048), (wGninthN3pXHT24Labs, wGninthN3pXHT24Nums, 2048),
    (wGninthN3pXHT25Labs, wGninthN3pXHT25Nums, 2048), (wGninthN3pXHT26Labs, wGninthN3pXHT26Nums,
    2048), (wGninthN3pXHT27Labs, wGninthN3pXHT27Nums, 2048), (wGninthN3pXHT28Labs,
    wGninthN3pXHT28Nums, 2048), (wGninthN3pXHT29Labs, wGninthN3pXHT29Nums, 2048),
    (wGninthN3pXHT30Labs, wGninthN3pXHT30Nums, 144)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

set_option maxRecDepth 100000 in
/-- The dense odd tensor part of the source (gident's `OddDense`, one pass over the source
chunks). -/
theorem wGninthN3pX_nlchk : OddDense.oddChk 64 ((2 ^ 3 - 1) * 2 ^ 0) false true
    [(wGninthN3pXHT0Labs, wGninthN3pXHT0Nums, 2048), (wGninthN3pXHT1Labs, wGninthN3pXHT1Nums,
    2048), (wGninthN3pXHT2Labs, wGninthN3pXHT2Nums, 2048), (wGninthN3pXHT3Labs,
    wGninthN3pXHT3Nums, 2048), (wGninthN3pXHT4Labs, wGninthN3pXHT4Nums, 2048),
    (wGninthN3pXHT5Labs, wGninthN3pXHT5Nums, 2048), (wGninthN3pXHT6Labs, wGninthN3pXHT6Nums,
    2048), (wGninthN3pXHT7Labs, wGninthN3pXHT7Nums, 2048), (wGninthN3pXHT8Labs,
    wGninthN3pXHT8Nums, 2048), (wGninthN3pXHT9Labs, wGninthN3pXHT9Nums, 2048),
    (wGninthN3pXHT10Labs, wGninthN3pXHT10Nums, 2048), (wGninthN3pXHT11Labs, wGninthN3pXHT11Nums,
    2048), (wGninthN3pXHT12Labs, wGninthN3pXHT12Nums, 2048), (wGninthN3pXHT13Labs,
    wGninthN3pXHT13Nums, 2048), (wGninthN3pXHT14Labs, wGninthN3pXHT14Nums, 2048),
    (wGninthN3pXHT15Labs, wGninthN3pXHT15Nums, 2048), (wGninthN3pXHT16Labs, wGninthN3pXHT16Nums,
    2048), (wGninthN3pXHT17Labs, wGninthN3pXHT17Nums, 2048), (wGninthN3pXHT18Labs,
    wGninthN3pXHT18Nums, 2048), (wGninthN3pXHT19Labs, wGninthN3pXHT19Nums, 2048),
    (wGninthN3pXHT20Labs, wGninthN3pXHT20Nums, 2048), (wGninthN3pXHT21Labs, wGninthN3pXHT21Nums,
    2048), (wGninthN3pXHT22Labs, wGninthN3pXHT22Nums, 2048), (wGninthN3pXHT23Labs,
    wGninthN3pXHT23Nums, 2048), (wGninthN3pXHT24Labs, wGninthN3pXHT24Nums, 2048),
    (wGninthN3pXHT25Labs, wGninthN3pXHT25Nums, 2048), (wGninthN3pXHT26Labs, wGninthN3pXHT26Nums,
    2048), (wGninthN3pXHT27Labs, wGninthN3pXHT27Nums, 2048), (wGninthN3pXHT28Labs,
    wGninthN3pXHT28Nums, 2048), (wGninthN3pXHT29Labs, wGninthN3pXHT29Nums, 2048),
    (wGninthN3pXHT30Labs, wGninthN3pXHT30Nums, 144)] wGninthN3pXGX0 (253952) = true := by
  decide +kernel

/-- The odd tensor part of the source. -/
theorem wGninthN3pX_nl : oddLZ 64 true wGninthN3pXGX0 wGninthN3pXL = 253952 :=
  OddDense.oddLZ_of_chk true wGninthN3pXL wGninthN3pXW _ wGninthN3pX_LshC (wGninthN3pXGX0_ten
      ((tensorWordDenAll wGninthN3pXG : ℚ) * 32)).symm (by decide +kernel)
    (by decide +kernel) wGninthN3pXGX0_bnd wGninthN3pX_nlchk

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem wGninthN3pX_v1 : tdotM 64 (trialityTensorT 64 (!true) wGninthN3pXHX0) wGninthN3pXGX0 =
    129024 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor self dot of the target. -/
theorem wGninthN3pX_v2 : tdotM 64 wGninthN3pXGX0 wGninthN3pXGX0 = 128000 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wGninthN3pX_ht : wGninthN3pXL.sden * (oddLZ 64 true wGninthN3pXGX0 wGninthN3pXL : ℚ) /
    (((tensorWordDenAll wGninthN3pXG : ℚ) * 32) / 2 ^ 9) +
    (tdotM 64 (trialityTensorT 64 (!true) wGninthN3pXHX0) wGninthN3pXGX0 : ℚ) / (2 *
        (((tensorWordDenAll wGninthN3pXH : ℚ) * 32) / 2 ^ 4) * (((tensorWordDenAll wGninthN3pXG :
        ℚ) * 32) / 2 ^ 9)) =
      (tdotM 64 wGninthN3pXGX0 wGninthN3pXGX0 : ℚ) / ((((tensorWordDenAll wGninthN3pXG : ℚ) * 32)
          / 2 ^ 9) * (((tensorWordDenAll wGninthN3pXG : ℚ) * 32) / 2 ^ 9)) := by
  rw [wGninthN3pX_nl, wGninthN3pX_v1, wGninthN3pX_v2]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
