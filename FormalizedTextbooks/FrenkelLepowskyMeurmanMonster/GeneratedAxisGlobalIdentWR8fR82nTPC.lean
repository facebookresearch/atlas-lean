/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR82nTChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR82nTTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (tensor) of the identification Root8[2]- <-> Tenth[38]+ (record r8f:R82-, e =
-1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The source short block as packed chunks. -/
theorem wR8fR82nT_LshC : wR8fR82nTL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wR8fR82nTHT0Labs, wR8fR82nTHT0Nums, 2048), (wR8fR82nTHT1Labs, wR8fR82nTHT1Nums, 2048),
    (wR8fR82nTHT2Labs, wR8fR82nTHT2Nums, 2048), (wR8fR82nTHT3Labs, wR8fR82nTHT3Nums, 2048),
    (wR8fR82nTHT4Labs, wR8fR82nTHT4Nums, 2048), (wR8fR82nTHT5Labs, wR8fR82nTHT5Nums, 2048),
    (wR8fR82nTHT6Labs, wR8fR82nTHT6Nums, 2048), (wR8fR82nTHT7Labs, wR8fR82nTHT7Nums, 2048),
    (wR8fR82nTHT8Labs, wR8fR82nTHT8Nums, 2048), (wR8fR82nTHT9Labs, wR8fR82nTHT9Nums, 2048),
    (wR8fR82nTHT10Labs, wR8fR82nTHT10Nums, 2048), (wR8fR82nTHT11Labs, wR8fR82nTHT11Nums, 2048),
    (wR8fR82nTHT12Labs, wR8fR82nTHT12Nums, 2048), (wR8fR82nTHT13Labs, wR8fR82nTHT13Nums, 2048),
    (wR8fR82nTHT14Labs, wR8fR82nTHT14Nums, 2048), (wR8fR82nTHT15Labs, wR8fR82nTHT15Nums, 2048),
    (wR8fR82nTHT16Labs, wR8fR82nTHT16Nums, 808)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

set_option maxRecDepth 100000 in
/-- The dense odd tensor part of the source (gident's `OddDense`, one pass over the source
chunks). -/
theorem wR8fR82nT_nlchk : OddDense.oddChk 64 ((2 ^ 4 - 1) * 2 ^ 0) true false [(wR8fR82nTHT0Labs,
    wR8fR82nTHT0Nums, 2048), (wR8fR82nTHT1Labs, wR8fR82nTHT1Nums, 2048), (wR8fR82nTHT2Labs,
    wR8fR82nTHT2Nums, 2048), (wR8fR82nTHT3Labs, wR8fR82nTHT3Nums, 2048), (wR8fR82nTHT4Labs,
    wR8fR82nTHT4Nums, 2048), (wR8fR82nTHT5Labs, wR8fR82nTHT5Nums, 2048), (wR8fR82nTHT6Labs,
    wR8fR82nTHT6Nums, 2048), (wR8fR82nTHT7Labs, wR8fR82nTHT7Nums, 2048), (wR8fR82nTHT8Labs,
    wR8fR82nTHT8Nums, 2048), (wR8fR82nTHT9Labs, wR8fR82nTHT9Nums, 2048), (wR8fR82nTHT10Labs,
    wR8fR82nTHT10Nums, 2048), (wR8fR82nTHT11Labs, wR8fR82nTHT11Nums, 2048), (wR8fR82nTHT12Labs,
    wR8fR82nTHT12Nums, 2048), (wR8fR82nTHT13Labs, wR8fR82nTHT13Nums, 2048), (wR8fR82nTHT14Labs,
    wR8fR82nTHT14Nums, 2048), (wR8fR82nTHT15Labs, wR8fR82nTHT15Nums, 2048), (wR8fR82nTHT16Labs,
    wR8fR82nTHT16Nums, 808)] wR8fR82nTGX0 (254976) = true := by
  decide +kernel

/-- The odd tensor part of the source. -/
theorem wR8fR82nT_nl : oddLZ 64 false wR8fR82nTGX0 wR8fR82nTL = 254976 :=
  OddDense.oddLZ_of_chk false wR8fR82nTL wR8fR82nTW _ wR8fR82nT_LshC (wR8fR82nTGX0_ten
      ((tensorWordDenAll wR8fR82nTG : ℚ) * 32)).symm (by decide +kernel)
    (by decide +kernel) wR8fR82nTGX0_bnd wR8fR82nT_nlchk

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem wR8fR82nT_v1 : tdotM 64 (trialityTensorT 64 (!false) wR8fR82nTHX0) wR8fR82nTGX0 = 129536
    := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor self dot of the target. -/
theorem wR8fR82nT_v2 : tdotM 64 wR8fR82nTGX0 wR8fR82nTGX0 = 128512 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wR8fR82nT_ht : wR8fR82nTL.sden * (oddLZ 64 false wR8fR82nTGX0 wR8fR82nTL : ℚ) /
    (((tensorWordDenAll wR8fR82nTG : ℚ) * 32) / 2 ^ 27) +
    (tdotM 64 (trialityTensorT 64 (!false) wR8fR82nTHX0) wR8fR82nTGX0 : ℚ) / (2 *
        (((tensorWordDenAll wR8fR82nTH : ℚ) * 32) / 2 ^ 12) * (((tensorWordDenAll wR8fR82nTG : ℚ)
        * 32) / 2 ^ 27)) =
      (tdotM 64 wR8fR82nTGX0 wR8fR82nTGX0 : ℚ) / ((((tensorWordDenAll wR8fR82nTG : ℚ) * 32) / 2 ^
          27) * (((tensorWordDenAll wR8fR82nTG : ℚ) * 32) / 2 ^ 27)) := by
  rw [wR8fR82nT_nl, wR8fR82nT_v1, wR8fR82nT_v2]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
