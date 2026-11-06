/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE9nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE9nTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG

/-! # Factory parts (tensor) of the identification Eighth[13]- <-> Eighth[13]- (record goctad:E9-,
e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wGoctadE9n_ht : wGoctadE9nL.sden * (oddLZ 64 false wGoctadE9nGXn wGoctadE9nL : ℚ) /
    ((tensorWordDenAll wGoctadE9nG : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) +
    (tdotM 64 (trialityTensorT 64 (!false) wGoctadE9nHXn) wGoctadE9nGXn : ℚ) / (2 *
        ((tensorWordDenAll wGoctadE9nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) *
        ((tensorWordDenAll wGoctadE9nG : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)))) =
      (tdotM 64 wGoctadE9nGXn wGoctadE9nGXn : ℚ) / (((tensorWordDenAll wGoctadE9nG : ℚ) * (2 *
          ((tensorWordDenAll srcEighthH : ℚ) * 1))) * ((tensorWordDenAll wGoctadE9nG : ℚ) * (2 *
          ((tensorWordDenAll srcEighthH : ℚ) * 1)))) := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
