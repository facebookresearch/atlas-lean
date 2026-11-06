/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS7c11nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS7c11nTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense

/-! # Factory parts (tensor) of the identification Seventh[18]- <-> Tenth[68]- (record
gforest:S7c11-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wGoctadXGforestS7c11n_ht : wGoctadXGforestS7c11nL.sden * (oddLZ 64 false
    wGoctadXGforestS7c11nGX0 wGoctadXGforestS7c11nL : ℚ) / (((tensorWordDenAll
    wGoctadXGforestS7c11nG : ℚ) * 32) / 2 ^ 9) +
    (tdotM 64 (trialityTensorT 64 (!false) wGoctadXGforestS7c11nHX0) wGoctadXGforestS7c11nGX0 : ℚ)
        / (2 * (((tensorWordDenAll wGoctadXGforestS7c11nH : ℚ) * srcSeventhD0) / 2 ^ 20) *
        (((tensorWordDenAll wGoctadXGforestS7c11nG : ℚ) * 32) / 2 ^ 9)) =
      (tdotM 64 wGoctadXGforestS7c11nGX0 wGoctadXGforestS7c11nGX0 : ℚ) / ((((tensorWordDenAll
          wGoctadXGforestS7c11nG : ℚ) * 32) / 2 ^ 9) * (((tensorWordDenAll wGoctadXGforestS7c11nG
          : ℚ) * 32) / 2 ^ 9)) := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
