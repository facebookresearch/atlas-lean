/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE4T26nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE4T26nTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (tensor) of the identification Eighth[8]- <-> Tenth[40]+ (record
goctad:E4@T26-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The source short block as packed chunks. -/
theorem wGoctadE4T26n_LshC : wGoctadE4T26nL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGoctadE4T26nHT0Labs, wGoctadE4T26nHT0Nums, 2048), (wGoctadE4T26nHT1Labs,
    wGoctadE4T26nHT1Nums, 2048), (wGoctadE4T26nHT2Labs, wGoctadE4T26nHT2Nums, 2048),
    (wGoctadE4T26nHT3Labs, wGoctadE4T26nHT3Nums, 2048), (wGoctadE4T26nHT4Labs,
    wGoctadE4T26nHT4Nums, 2048), (wGoctadE4T26nHT5Labs, wGoctadE4T26nHT5Nums, 2048),
    (wGoctadE4T26nHT6Labs, wGoctadE4T26nHT6Nums, 2048), (wGoctadE4T26nHT7Labs,
    wGoctadE4T26nHT7Nums, 2048), (wGoctadE4T26nHT8Labs, wGoctadE4T26nHT8Nums, 2048),
    (wGoctadE4T26nHT9Labs, wGoctadE4T26nHT9Nums, 2048), (wGoctadE4T26nHT10Labs,
    wGoctadE4T26nHT10Nums, 2048), (wGoctadE4T26nHT11Labs, wGoctadE4T26nHT11Nums, 2048),
    (wGoctadE4T26nHT12Labs, wGoctadE4T26nHT12Nums, 2048), (wGoctadE4T26nHT13Labs,
    wGoctadE4T26nHT13Nums, 2048), (wGoctadE4T26nHT14Labs, wGoctadE4T26nHT14Nums, 2048),
    (wGoctadE4T26nHT15Labs, wGoctadE4T26nHT15Nums, 2048), (wGoctadE4T26nHT16Labs,
    wGoctadE4T26nHT16Nums, 2048), (wGoctadE4T26nHT17Labs, wGoctadE4T26nHT17Nums, 2048),
    (wGoctadE4T26nHT18Labs, wGoctadE4T26nHT18Nums, 2048), (wGoctadE4T26nHT19Labs,
    wGoctadE4T26nHT19Nums, 2048), (wGoctadE4T26nHT20Labs, wGoctadE4T26nHT20Nums, 2048),
    (wGoctadE4T26nHT21Labs, wGoctadE4T26nHT21Nums, 668)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

set_option maxRecDepth 100000 in
/-- The dense odd tensor part of the source (gident's `OddDense`, one pass over the source
chunks). -/
theorem wGoctadE4T26n_nlchk : OddDense.oddChk 64 ((2 ^ 4 - 1) * 2 ^ 0) true false
    [(wGoctadE4T26nHT0Labs, wGoctadE4T26nHT0Nums, 2048), (wGoctadE4T26nHT1Labs,
    wGoctadE4T26nHT1Nums, 2048), (wGoctadE4T26nHT2Labs, wGoctadE4T26nHT2Nums, 2048),
    (wGoctadE4T26nHT3Labs, wGoctadE4T26nHT3Nums, 2048), (wGoctadE4T26nHT4Labs,
    wGoctadE4T26nHT4Nums, 2048), (wGoctadE4T26nHT5Labs, wGoctadE4T26nHT5Nums, 2048),
    (wGoctadE4T26nHT6Labs, wGoctadE4T26nHT6Nums, 2048), (wGoctadE4T26nHT7Labs,
    wGoctadE4T26nHT7Nums, 2048), (wGoctadE4T26nHT8Labs, wGoctadE4T26nHT8Nums, 2048),
    (wGoctadE4T26nHT9Labs, wGoctadE4T26nHT9Nums, 2048), (wGoctadE4T26nHT10Labs,
    wGoctadE4T26nHT10Nums, 2048), (wGoctadE4T26nHT11Labs, wGoctadE4T26nHT11Nums, 2048),
    (wGoctadE4T26nHT12Labs, wGoctadE4T26nHT12Nums, 2048), (wGoctadE4T26nHT13Labs,
    wGoctadE4T26nHT13Nums, 2048), (wGoctadE4T26nHT14Labs, wGoctadE4T26nHT14Nums, 2048),
    (wGoctadE4T26nHT15Labs, wGoctadE4T26nHT15Nums, 2048), (wGoctadE4T26nHT16Labs,
    wGoctadE4T26nHT16Nums, 2048), (wGoctadE4T26nHT17Labs, wGoctadE4T26nHT17Nums, 2048),
    (wGoctadE4T26nHT18Labs, wGoctadE4T26nHT18Nums, 2048), (wGoctadE4T26nHT19Labs,
    wGoctadE4T26nHT19Nums, 2048), (wGoctadE4T26nHT20Labs, wGoctadE4T26nHT20Nums, 2048),
    (wGoctadE4T26nHT21Labs, wGoctadE4T26nHT21Nums, 668)] wGoctadE4T26nGX0 (65024) = true := by
  decide +kernel

/-- The odd tensor part of the source. -/
theorem wGoctadE4T26n_nl : oddLZ 64 false wGoctadE4T26nGX0 wGoctadE4T26nL = 65024 :=
  OddDense.oddLZ_of_chk false wGoctadE4T26nL wGoctadE4T26nW _ wGoctadE4T26n_LshC
      (wGoctadE4T26nGX0_ten ((tensorWordDenAll wGoctadE4T26nG : ℚ) * 32)).symm (by decide +kernel)
    (by decide +kernel) wGoctadE4T26nGX0_bnd wGoctadE4T26n_nlchk

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem wGoctadE4T26n_v1 : tdotM 64 (trialityTensorT 64 (!false) wGoctadE4T26nHX0)
    wGoctadE4T26nGX0 = 126976 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor self dot of the target. -/
theorem wGoctadE4T26n_v2 : tdotM 64 wGoctadE4T26nGX0 wGoctadE4T26nGX0 = 128512 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wGoctadE4T26n_ht : wGoctadE4T26nL.sden * (oddLZ 64 false wGoctadE4T26nGX0 wGoctadE4T26nL :
    ℚ) / (((tensorWordDenAll wGoctadE4T26nG : ℚ) * 32) / 2 ^ 25) +
    (tdotM 64 (trialityTensorT 64 (!false) wGoctadE4T26nHX0) wGoctadE4T26nGX0 : ℚ) / (2 *
        (((tensorWordDenAll wGoctadE4T26nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) /
        2 ^ 29) * (((tensorWordDenAll wGoctadE4T26nG : ℚ) * 32) / 2 ^ 25)) =
      (tdotM 64 wGoctadE4T26nGX0 wGoctadE4T26nGX0 : ℚ) / ((((tensorWordDenAll wGoctadE4T26nG : ℚ)
          * 32) / 2 ^ 25) * (((tensorWordDenAll wGoctadE4T26nG : ℚ) * 32) / 2 ^ 25)) := by
  rw [wGoctadE4T26n_nl, wGoctadE4T26n_v1, wGoctadE4T26n_v2]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
