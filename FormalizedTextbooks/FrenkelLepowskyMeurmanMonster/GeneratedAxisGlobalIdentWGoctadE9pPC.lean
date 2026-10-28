/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE9pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE9pTX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddG

/-! # Factory parts (tensor) of the identification Eighth[13]+ <-> Seventh[14]+ (record
goctad:E9+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target
(normalized tensors). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wGoctadE9p_ht : wGoctadE9pL.sden * (oddLZ 64 true wGoctadE9pGXn wGoctadE9pL : ℚ) /
    ((tensorWordDenAll wGoctadE9pG : ℚ) * srcSeventhD0) +
    (tdotM 64 (trialityTensorT 64 (!true) wGoctadE9pHXn) wGoctadE9pGXn : ℚ) / (2 *
        ((tensorWordDenAll wGoctadE9pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))) *
        ((tensorWordDenAll wGoctadE9pG : ℚ) * srcSeventhD0)) =
      (tdotM 64 wGoctadE9pGXn wGoctadE9pGXn : ℚ) / (((tensorWordDenAll wGoctadE9pG : ℚ) *
          srcSeventhD0) * ((tensorWordDenAll wGoctadE9pG : ℚ) * srcSeventhD0)) := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
