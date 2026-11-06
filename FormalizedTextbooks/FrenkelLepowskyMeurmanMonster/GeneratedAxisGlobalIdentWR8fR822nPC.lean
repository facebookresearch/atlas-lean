/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR822nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Factory parts (tensor) of the identification Root8[4]- <-> Root8[4]- (record r8f:R822-, e =
-1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wR8fR822n_ht : wR8fR822nL.sden * (oddLZ 64 false wR8fR822nGX wR8fR822nL : ℚ) /
    ((tensorWordDenAll wR8fR822nG : ℚ) * 32) +
    (tdotM 64 (trialityTensorT 64 (!false) wR8fR822nHX) wR8fR822nGX : ℚ) / (2 * ((tensorWordDenAll
        wR8fR822nH : ℚ) * 32) * ((tensorWordDenAll wR8fR822nG : ℚ) * 32)) =
      (tdotM 64 wR8fR822nGX wR8fR822nGX : ℚ) / (((tensorWordDenAll wR8fR822nG : ℚ) * 32) *
          ((tensorWordDenAll wR8fR822nG : ℚ) * 32)) := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
