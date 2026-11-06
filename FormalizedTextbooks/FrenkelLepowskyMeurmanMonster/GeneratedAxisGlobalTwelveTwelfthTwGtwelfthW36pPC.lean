/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW36pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (tensor) of the identification Twelfth[36]+ <-> Twelfth[36]+ (record
gtwelfth:W36+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem twGtwelfthW36p_ht : twGtwelfthW36pL.sden * (oddLZ 64 true twGtwelfthW36pGX twGtwelfthW36pL
    : ℚ) / ((tensorWordDenAll twGtwelfthW36pG : ℚ) * 32) +
    (tdotM 64 (trialityTensorT 64 (!true) twGtwelfthW36pHX) twGtwelfthW36pGX : ℚ) / (2 *
        ((tensorWordDenAll twGtwelfthW36pH : ℚ) * 32) * ((tensorWordDenAll twGtwelfthW36pG : ℚ) *
        32)) =
      (tdotM 64 twGtwelfthW36pGX twGtwelfthW36pGX : ℚ) / (((tensorWordDenAll twGtwelfthW36pG : ℚ)
          * 32) * ((tensorWordDenAll twGtwelfthW36pG : ℚ) * 32)) := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
