/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR817pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcRootEightCF

/-! # Factory parts (tensor) of the identification Root8[26]+ <-> Root8[26]+ (record r8f:R817+, e
= 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wR8fR817p_ht : wR8fR817pL.sden * (oddLZ 64 true wR8fR817pGX wR8fR817pL : ℚ) /
    ((tensorWordDenAll wR8fR817pG : ℚ) * 32) +
    (tdotM 64 (trialityTensorT 64 (!true) wR8fR817pHX) wR8fR817pGX : ℚ) / (2 * ((tensorWordDenAll
        wR8fR817pH : ℚ) * 32) * ((tensorWordDenAll wR8fR817pG : ℚ) * 32)) =
      (tdotM 64 wR8fR817pGX wR8fR817pGX : ℚ) / (((tensorWordDenAll wR8fR817pG : ℚ) * 32) *
          ((tensorWordDenAll wR8fR817pG : ℚ) * 32)) := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
