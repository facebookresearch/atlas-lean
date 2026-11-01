/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN7nXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN7nXTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (tensor) of the identification Fifth[4]+ <-> Ninth[12]- (record gninth:N7-, e
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
theorem wGninthN7nX_LshC : wGninthN7nXL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGninthN7nXHT0Labs, wGninthN7nXHT0Nums, 2048), (wGninthN7nXHT1Labs, wGninthN7nXHT1Nums,
    2048), (wGninthN7nXHT2Labs, wGninthN7nXHT2Nums, 2048), (wGninthN7nXHT3Labs,
    wGninthN7nXHT3Nums, 2048), (wGninthN7nXHT4Labs, wGninthN7nXHT4Nums, 2048),
    (wGninthN7nXHT5Labs, wGninthN7nXHT5Nums, 2048), (wGninthN7nXHT6Labs, wGninthN7nXHT6Nums,
    2048), (wGninthN7nXHT7Labs, wGninthN7nXHT7Nums, 2048), (wGninthN7nXHT8Labs,
    wGninthN7nXHT8Nums, 2048), (wGninthN7nXHT9Labs, wGninthN7nXHT9Nums, 2048),
    (wGninthN7nXHT10Labs, wGninthN7nXHT10Nums, 2048), (wGninthN7nXHT11Labs, wGninthN7nXHT11Nums,
    2048), (wGninthN7nXHT12Labs, wGninthN7nXHT12Nums, 2048), (wGninthN7nXHT13Labs,
    wGninthN7nXHT13Nums, 2048), (wGninthN7nXHT14Labs, wGninthN7nXHT14Nums, 2048),
    (wGninthN7nXHT15Labs, wGninthN7nXHT15Nums, 2048), (wGninthN7nXHT16Labs, wGninthN7nXHT16Nums,
    2048), (wGninthN7nXHT17Labs, wGninthN7nXHT17Nums, 2048), (wGninthN7nXHT18Labs,
    wGninthN7nXHT18Nums, 2048), (wGninthN7nXHT19Labs, wGninthN7nXHT19Nums, 2048),
    (wGninthN7nXHT20Labs, wGninthN7nXHT20Nums, 2048), (wGninthN7nXHT21Labs, wGninthN7nXHT21Nums,
    2048), (wGninthN7nXHT22Labs, wGninthN7nXHT22Nums, 2048), (wGninthN7nXHT23Labs,
    wGninthN7nXHT23Nums, 2048), (wGninthN7nXHT24Labs, wGninthN7nXHT24Nums, 2048),
    (wGninthN7nXHT25Labs, wGninthN7nXHT25Nums, 2048), (wGninthN7nXHT26Labs, wGninthN7nXHT26Nums,
    2048), (wGninthN7nXHT27Labs, wGninthN7nXHT27Nums, 2048), (wGninthN7nXHT28Labs,
    wGninthN7nXHT28Nums, 2048), (wGninthN7nXHT29Labs, wGninthN7nXHT29Nums, 2048),
    (wGninthN7nXHT30Labs, wGninthN7nXHT30Nums, 144)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

set_option maxRecDepth 100000 in
/-- The dense odd tensor part of the source (gident's `OddDense`, one pass over the source
chunks). -/
theorem wGninthN7nX_nlchk : OddDense.oddChk 64 ((2 ^ 1 - 1) * 2 ^ 0) true false
    [(wGninthN7nXHT0Labs, wGninthN7nXHT0Nums, 2048), (wGninthN7nXHT1Labs, wGninthN7nXHT1Nums,
    2048), (wGninthN7nXHT2Labs, wGninthN7nXHT2Nums, 2048), (wGninthN7nXHT3Labs,
    wGninthN7nXHT3Nums, 2048), (wGninthN7nXHT4Labs, wGninthN7nXHT4Nums, 2048),
    (wGninthN7nXHT5Labs, wGninthN7nXHT5Nums, 2048), (wGninthN7nXHT6Labs, wGninthN7nXHT6Nums,
    2048), (wGninthN7nXHT7Labs, wGninthN7nXHT7Nums, 2048), (wGninthN7nXHT8Labs,
    wGninthN7nXHT8Nums, 2048), (wGninthN7nXHT9Labs, wGninthN7nXHT9Nums, 2048),
    (wGninthN7nXHT10Labs, wGninthN7nXHT10Nums, 2048), (wGninthN7nXHT11Labs, wGninthN7nXHT11Nums,
    2048), (wGninthN7nXHT12Labs, wGninthN7nXHT12Nums, 2048), (wGninthN7nXHT13Labs,
    wGninthN7nXHT13Nums, 2048), (wGninthN7nXHT14Labs, wGninthN7nXHT14Nums, 2048),
    (wGninthN7nXHT15Labs, wGninthN7nXHT15Nums, 2048), (wGninthN7nXHT16Labs, wGninthN7nXHT16Nums,
    2048), (wGninthN7nXHT17Labs, wGninthN7nXHT17Nums, 2048), (wGninthN7nXHT18Labs,
    wGninthN7nXHT18Nums, 2048), (wGninthN7nXHT19Labs, wGninthN7nXHT19Nums, 2048),
    (wGninthN7nXHT20Labs, wGninthN7nXHT20Nums, 2048), (wGninthN7nXHT21Labs, wGninthN7nXHT21Nums,
    2048), (wGninthN7nXHT22Labs, wGninthN7nXHT22Nums, 2048), (wGninthN7nXHT23Labs,
    wGninthN7nXHT23Nums, 2048), (wGninthN7nXHT24Labs, wGninthN7nXHT24Nums, 2048),
    (wGninthN7nXHT25Labs, wGninthN7nXHT25Nums, 2048), (wGninthN7nXHT26Labs, wGninthN7nXHT26Nums,
    2048), (wGninthN7nXHT27Labs, wGninthN7nXHT27Nums, 2048), (wGninthN7nXHT28Labs,
    wGninthN7nXHT28Nums, 2048), (wGninthN7nXHT29Labs, wGninthN7nXHT29Nums, 2048),
    (wGninthN7nXHT30Labs, wGninthN7nXHT30Nums, 144)] wGninthN7nXGX0 (131072) = true := by
  decide +kernel

/-- The odd tensor part of the source. -/
theorem wGninthN7nX_nl : oddLZ 64 false wGninthN7nXGX0 wGninthN7nXL = 131072 :=
  OddDense.oddLZ_of_chk false wGninthN7nXL wGninthN7nXW _ wGninthN7nX_LshC (wGninthN7nXGX0_ten
      ((tensorWordDenAll wGninthN7nXG : ℚ) * 1)).symm (by decide +kernel)
    (by decide +kernel) wGninthN7nXGX0_bnd wGninthN7nX_nlchk

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem wGninthN7nX_v1 : tdotM 64 (trialityTensorT 64 (!false) wGninthN7nXHX0) wGninthN7nXGX0 =
    65536 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor self dot of the target. -/
theorem wGninthN7nX_v2 : tdotM 64 wGninthN7nXGX0 wGninthN7nXGX0 = 32768 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wGninthN7nX_ht : wGninthN7nXL.sden * (oddLZ 64 false wGninthN7nXGX0 wGninthN7nXL : ℚ) /
    (((tensorWordDenAll wGninthN7nXG : ℚ) * 1) / 2 ^ 13) +
    (tdotM 64 (trialityTensorT 64 (!false) wGninthN7nXHX0) wGninthN7nXGX0 : ℚ) / (2 *
        (((tensorWordDenAll wGninthN7nXH : ℚ) * 32) / 2 ^ 16) * (((tensorWordDenAll wGninthN7nXG :
        ℚ) * 1) / 2 ^ 13)) =
      (tdotM 64 wGninthN7nXGX0 wGninthN7nXGX0 : ℚ) / ((((tensorWordDenAll wGninthN7nXG : ℚ) * 1) /
          2 ^ 13) * (((tensorWordDenAll wGninthN7nXG : ℚ) * 1) / 2 ^ 13)) := by
  rw [wGninthN7nX_nl, wGninthN7nX_v1, wGninthN7nX_v2]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
