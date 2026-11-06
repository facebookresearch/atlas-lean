/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE34T21nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE34T21nTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (tensor) of the identification Eighth[47]- <-> Tenth[26]+ (record
goctad:E34@T21-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The source short block as packed chunks. -/
theorem wGoctadE34T21n_LshC : wGoctadE34T21nL.sh = ShortData.ofList (OctadDense.octChunkTerms
    [(wGoctadE34T21nHT0Labs, wGoctadE34T21nHT0Nums, 2048), (wGoctadE34T21nHT1Labs,
    wGoctadE34T21nHT1Nums, 2048), (wGoctadE34T21nHT2Labs, wGoctadE34T21nHT2Nums, 2048),
    (wGoctadE34T21nHT3Labs, wGoctadE34T21nHT3Nums, 2048), (wGoctadE34T21nHT4Labs,
    wGoctadE34T21nHT4Nums, 2048), (wGoctadE34T21nHT5Labs, wGoctadE34T21nHT5Nums, 2048),
    (wGoctadE34T21nHT6Labs, wGoctadE34T21nHT6Nums, 2048), (wGoctadE34T21nHT7Labs,
    wGoctadE34T21nHT7Nums, 2048), (wGoctadE34T21nHT8Labs, wGoctadE34T21nHT8Nums, 2048),
    (wGoctadE34T21nHT9Labs, wGoctadE34T21nHT9Nums, 2048), (wGoctadE34T21nHT10Labs,
    wGoctadE34T21nHT10Nums, 2048), (wGoctadE34T21nHT11Labs, wGoctadE34T21nHT11Nums, 2048),
    (wGoctadE34T21nHT12Labs, wGoctadE34T21nHT12Nums, 2048), (wGoctadE34T21nHT13Labs,
    wGoctadE34T21nHT13Nums, 2048), (wGoctadE34T21nHT14Labs, wGoctadE34T21nHT14Nums, 2048),
    (wGoctadE34T21nHT15Labs, wGoctadE34T21nHT15Nums, 2048), (wGoctadE34T21nHT16Labs,
    wGoctadE34T21nHT16Nums, 2048), (wGoctadE34T21nHT17Labs, wGoctadE34T21nHT17Nums, 2048),
    (wGoctadE34T21nHT18Labs, wGoctadE34T21nHT18Nums, 2048), (wGoctadE34T21nHT19Labs,
    wGoctadE34T21nHT19Nums, 2048), (wGoctadE34T21nHT20Labs, wGoctadE34T21nHT20Nums, 2048),
    (wGoctadE34T21nHT21Labs, wGoctadE34T21nHT21Nums, 668)]) := by
  simp only [OctadDense.octChunkTerms, List.append_nil]
  rfl

set_option maxRecDepth 100000 in
/-- The dense odd tensor part of the source (gident's `OddDense`, one pass over the source
chunks). -/
theorem wGoctadE34T21n_nlchk : OddDense.oddChk 72 ((2 ^ 4 - 1) * 2 ^ 0) true false
    [(wGoctadE34T21nHT0Labs, wGoctadE34T21nHT0Nums, 2048), (wGoctadE34T21nHT1Labs,
    wGoctadE34T21nHT1Nums, 2048), (wGoctadE34T21nHT2Labs, wGoctadE34T21nHT2Nums, 2048),
    (wGoctadE34T21nHT3Labs, wGoctadE34T21nHT3Nums, 2048), (wGoctadE34T21nHT4Labs,
    wGoctadE34T21nHT4Nums, 2048), (wGoctadE34T21nHT5Labs, wGoctadE34T21nHT5Nums, 2048),
    (wGoctadE34T21nHT6Labs, wGoctadE34T21nHT6Nums, 2048), (wGoctadE34T21nHT7Labs,
    wGoctadE34T21nHT7Nums, 2048), (wGoctadE34T21nHT8Labs, wGoctadE34T21nHT8Nums, 2048),
    (wGoctadE34T21nHT9Labs, wGoctadE34T21nHT9Nums, 2048), (wGoctadE34T21nHT10Labs,
    wGoctadE34T21nHT10Nums, 2048), (wGoctadE34T21nHT11Labs, wGoctadE34T21nHT11Nums, 2048),
    (wGoctadE34T21nHT12Labs, wGoctadE34T21nHT12Nums, 2048), (wGoctadE34T21nHT13Labs,
    wGoctadE34T21nHT13Nums, 2048), (wGoctadE34T21nHT14Labs, wGoctadE34T21nHT14Nums, 2048),
    (wGoctadE34T21nHT15Labs, wGoctadE34T21nHT15Nums, 2048), (wGoctadE34T21nHT16Labs,
    wGoctadE34T21nHT16Nums, 2048), (wGoctadE34T21nHT17Labs, wGoctadE34T21nHT17Nums, 2048),
    (wGoctadE34T21nHT18Labs, wGoctadE34T21nHT18Nums, 2048), (wGoctadE34T21nHT19Labs,
    wGoctadE34T21nHT19Nums, 2048), (wGoctadE34T21nHT20Labs, wGoctadE34T21nHT20Nums, 2048),
    (wGoctadE34T21nHT21Labs, wGoctadE34T21nHT21Nums, 668)] wGoctadE34T21nGX0 (65024) = true := by
  decide +kernel

/-- The odd tensor part of the source. -/
theorem wGoctadE34T21n_nl : oddLZ 72 false wGoctadE34T21nGX0 wGoctadE34T21nL = 65024 :=
  OddDense.oddLZ_of_chk false wGoctadE34T21nL wGoctadE34T21nW _ wGoctadE34T21n_LshC
      (wGoctadE34T21nGX0_ten ((tensorWordDenAll wGoctadE34T21nG : ℚ) * 32)).symm (by
      decide +kernel)
    (by decide +kernel) wGoctadE34T21nGX0_bnd wGoctadE34T21n_nlchk

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem wGoctadE34T21n_v1 : tdotM 72 (trialityTensorT 72 (!false) wGoctadE34T21nHX0)
    wGoctadE34T21nGX0 = 126976 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor self dot of the target. -/
theorem wGoctadE34T21n_v2 : tdotM 72 wGoctadE34T21nGX0 wGoctadE34T21nGX0 = 128512 := by
    decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wGoctadE34T21n_ht : wGoctadE34T21nL.sden * (oddLZ 72 false wGoctadE34T21nGX0
    wGoctadE34T21nL : ℚ) / (((tensorWordDenAll wGoctadE34T21nG : ℚ) * 32) / 2 ^ 17) +
    (tdotM 72 (trialityTensorT 72 (!false) wGoctadE34T21nHX0) wGoctadE34T21nGX0 : ℚ) / (2 *
        (((tensorWordDenAll wGoctadE34T21nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)))
        / 2 ^ 33) * (((tensorWordDenAll wGoctadE34T21nG : ℚ) * 32) / 2 ^ 17)) =
      (tdotM 72 wGoctadE34T21nGX0 wGoctadE34T21nGX0 : ℚ) / ((((tensorWordDenAll wGoctadE34T21nG :
          ℚ) * 32) / 2 ^ 17) * (((tensorWordDenAll wGoctadE34T21nG : ℚ) * 32) / 2 ^ 17)) := by
  rw [wGoctadE34T21n_nl, wGoctadE34T21n_v1, wGoctadE34T21n_v2]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
