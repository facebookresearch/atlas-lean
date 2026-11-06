/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86pPAm
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86pPAp
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86pPAp3

/-! # Factory parts (matrix, pairs) of the identification Root8[12]+ <-> Twelfth[34]- (record
r8f:R86+, e = 1)

The pair part of the pairing from its two integer sums and the pair self sum. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The pair part equals the pair self part of the target. -/
theorem wR8fR86p_hp : pairSumQ true wR8fR86pL wR8fR86pW = wR8fR86pW.sden * (selfPairsZ wR8fR86pW :
    ℚ) := by
  rw [pairSumQ_of_chk true wR8fR86pL wR8fR86pW (srcRootEightMatZc.act wR8fR86pH)
      (srcRootEightMat_act_entryZc wR8fR86pH) wR8fR86p_pchk, wR8fR86p_ps]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
