/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR822nPAm
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR822nPAp
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR822nPAp3

/-! # Factory parts (matrix, pairs) of the identification Root8[4]- <-> Root8[4]- (record
r8f:R822-, e = -1)

The pair part of the pairing from its two integer sums and the pair self sum. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The pair part equals the pair self part of the target. -/
theorem wR8fR822n_hp : pairSumQ false wR8fR822nL wR8fR822nW = wR8fR822nW.sden * (selfPairsZ
    wR8fR822nW : ℚ) := by
  rw [pairSumQ_of_chk false wR8fR822nL wR8fR822nW (srcRootEightMatZc.act wR8fR822nH)
      (srcRootEightMat_act_entryZc wR8fR822nH) wR8fR822n_pchk, wR8fR822n_ps]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
