/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR821nwChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Factory parts (tensor) of the identification Root8[33]- <-> Root8[33]- (record r8f:R821-, e
= -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The tensor part equals the tensor self part of the target. -/
theorem wR8fR821nw_ht : wR8fR821nwL.sden * (oddLZ 96 false wR8fR821nwGX wR8fR821nwL : ℚ) /
    ((tensorWordDenAll wR8fR821nwG : ℚ) * 32) +
    (tdotM 96 (trialityTensorT 96 (!false) wR8fR821nwHX) wR8fR821nwGX : ℚ) / (2 *
        ((tensorWordDenAll wR8fR821nwH : ℚ) * 32) * ((tensorWordDenAll wR8fR821nwG : ℚ) * 32)) =
      (tdotM 96 wR8fR821nwGX wR8fR821nwGX : ℚ) / (((tensorWordDenAll wR8fR821nwG : ℚ) * 32) *
          ((tensorWordDenAll wR8fR821nwG : ℚ) * 32)) := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
