/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN6pXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN6pXTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (tensor) of the identification Ninth[10]+ <-> Twelfth[12]- (record gninth:N6+,
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
theorem wGninthN6pX_LshC : wGninthN6pXL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN6pXHT0Labs, wGninthN6pXHT0Nums, 2048), (wGninthN6pXHT1Labs, wGninthN6pXHT1Nums,
    2048), (wGninthN6pXHT2Labs, wGninthN6pXHT2Nums, 2048), (wGninthN6pXHT3Labs,
    wGninthN6pXHT3Nums, 2048), (wGninthN6pXHT4Labs, wGninthN6pXHT4Nums, 2048),
    (wGninthN6pXHT5Labs, wGninthN6pXHT5Nums, 2048), (wGninthN6pXHT6Labs, wGninthN6pXHT6Nums,
    2048), (wGninthN6pXHT7Labs, wGninthN6pXHT7Nums, 2048), (wGninthN6pXHT8Labs,
    wGninthN6pXHT8Nums, 2048), (wGninthN6pXHT9Labs, wGninthN6pXHT9Nums, 2048),
    (wGninthN6pXHT10Labs, wGninthN6pXHT10Nums, 2048), (wGninthN6pXHT11Labs, wGninthN6pXHT11Nums,
    2048), (wGninthN6pXHT12Labs, wGninthN6pXHT12Nums, 2048), (wGninthN6pXHT13Labs,
    wGninthN6pXHT13Nums, 2048), (wGninthN6pXHT14Labs, wGninthN6pXHT14Nums, 2048),
    (wGninthN6pXHT15Labs, wGninthN6pXHT15Nums, 2048), (wGninthN6pXHT16Labs, wGninthN6pXHT16Nums,
    2048), (wGninthN6pXHT17Labs, wGninthN6pXHT17Nums, 2048), (wGninthN6pXHT18Labs,
    wGninthN6pXHT18Nums, 2048), (wGninthN6pXHT19Labs, wGninthN6pXHT19Nums, 2048),
    (wGninthN6pXHT20Labs, wGninthN6pXHT20Nums, 2048), (wGninthN6pXHT21Labs, wGninthN6pXHT21Nums,
    2048), (wGninthN6pXHT22Labs, wGninthN6pXHT22Nums, 2048), (wGninthN6pXHT23Labs,
    wGninthN6pXHT23Nums, 2048), (wGninthN6pXHT24Labs, wGninthN6pXHT24Nums, 2048),
    (wGninthN6pXHT25Labs, wGninthN6pXHT25Nums, 2048), (wGninthN6pXHT26Labs, wGninthN6pXHT26Nums,
    2048), (wGninthN6pXHT27Labs, wGninthN6pXHT27Nums, 2048), (wGninthN6pXHT28Labs,
    wGninthN6pXHT28Nums, 2048), (wGninthN6pXHT29Labs, wGninthN6pXHT29Nums, 2048),
    (wGninthN6pXHT30Labs, wGninthN6pXHT30Nums, 144)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

set_option maxRecDepth 100000 in
/-- The dense odd tensor part of the source (gident's `OddDense`, one pass over the source
chunks). -/
theorem wGninthN6pX_nlchk : OddDense.oddChk 64 ((2 ^ 3 - 1) * 2 ^ 0) false true
    [(wGninthN6pXHT0Labs, wGninthN6pXHT0Nums, 2048), (wGninthN6pXHT1Labs, wGninthN6pXHT1Nums,
    2048), (wGninthN6pXHT2Labs, wGninthN6pXHT2Nums, 2048), (wGninthN6pXHT3Labs,
    wGninthN6pXHT3Nums, 2048), (wGninthN6pXHT4Labs, wGninthN6pXHT4Nums, 2048),
    (wGninthN6pXHT5Labs, wGninthN6pXHT5Nums, 2048), (wGninthN6pXHT6Labs, wGninthN6pXHT6Nums,
    2048), (wGninthN6pXHT7Labs, wGninthN6pXHT7Nums, 2048), (wGninthN6pXHT8Labs,
    wGninthN6pXHT8Nums, 2048), (wGninthN6pXHT9Labs, wGninthN6pXHT9Nums, 2048),
    (wGninthN6pXHT10Labs, wGninthN6pXHT10Nums, 2048), (wGninthN6pXHT11Labs, wGninthN6pXHT11Nums,
    2048), (wGninthN6pXHT12Labs, wGninthN6pXHT12Nums, 2048), (wGninthN6pXHT13Labs,
    wGninthN6pXHT13Nums, 2048), (wGninthN6pXHT14Labs, wGninthN6pXHT14Nums, 2048),
    (wGninthN6pXHT15Labs, wGninthN6pXHT15Nums, 2048), (wGninthN6pXHT16Labs, wGninthN6pXHT16Nums,
    2048), (wGninthN6pXHT17Labs, wGninthN6pXHT17Nums, 2048), (wGninthN6pXHT18Labs,
    wGninthN6pXHT18Nums, 2048), (wGninthN6pXHT19Labs, wGninthN6pXHT19Nums, 2048),
    (wGninthN6pXHT20Labs, wGninthN6pXHT20Nums, 2048), (wGninthN6pXHT21Labs, wGninthN6pXHT21Nums,
    2048), (wGninthN6pXHT22Labs, wGninthN6pXHT22Nums, 2048), (wGninthN6pXHT23Labs,
    wGninthN6pXHT23Nums, 2048), (wGninthN6pXHT24Labs, wGninthN6pXHT24Nums, 2048),
    (wGninthN6pXHT25Labs, wGninthN6pXHT25Nums, 2048), (wGninthN6pXHT26Labs, wGninthN6pXHT26Nums,
    2048), (wGninthN6pXHT27Labs, wGninthN6pXHT27Nums, 2048), (wGninthN6pXHT28Labs,
    wGninthN6pXHT28Nums, 2048), (wGninthN6pXHT29Labs, wGninthN6pXHT29Nums, 2048),
    (wGninthN6pXHT30Labs, wGninthN6pXHT30Nums, 144)] wGninthN6pXGX0 (253952) = true := by
  decide +kernel

/-- The odd tensor part of the source. -/
theorem wGninthN6pX_nl : oddLZ 64 true wGninthN6pXGX0 wGninthN6pXL = 253952 :=
  OddDense.oddLZ_of_chk true wGninthN6pXL wGninthN6pXW _ wGninthN6pX_LshC (wGninthN6pXGX0_ten
      ((tensorWordDenAll wGninthN6pXG : ℚ) * 32)).symm (by decide +kernel)
    (by decide +kernel) wGninthN6pXGX0_bnd wGninthN6pX_nlchk

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem wGninthN6pX_v1 : tdotM 64 (trialityTensorT 64 (!true) wGninthN6pXHX0) wGninthN6pXGX0 =
    129024 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor self dot of the target. -/
theorem wGninthN6pX_v2 : tdotM 64 wGninthN6pXGX0 wGninthN6pXGX0 = 128000 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wGninthN6pX_ht : wGninthN6pXL.sden * (oddLZ 64 true wGninthN6pXGX0 wGninthN6pXL : ℚ) /
    (((tensorWordDenAll wGninthN6pXG : ℚ) * 32) / 2 ^ 9) +
    (tdotM 64 (trialityTensorT 64 (!true) wGninthN6pXHX0) wGninthN6pXGX0 : ℚ) / (2 *
        (((tensorWordDenAll wGninthN6pXH : ℚ) * 32) / 2 ^ 16) * (((tensorWordDenAll wGninthN6pXG :
        ℚ) * 32) / 2 ^ 9)) =
      (tdotM 64 wGninthN6pXGX0 wGninthN6pXGX0 : ℚ) / ((((tensorWordDenAll wGninthN6pXG : ℚ) * 32)
          / 2 ^ 9) * (((tensorWordDenAll wGninthN6pXG : ℚ) * 32) / 2 ^ 9)) := by
  rw [wGninthN6pX_nl, wGninthN6pX_v1, wGninthN6pX_v2]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
