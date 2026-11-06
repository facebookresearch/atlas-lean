/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR81pPAm
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR81pPAp
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR81pPAp3

/-! # Factory parts (matrix, pairs) of the identification Root8[16]+ <-> Twelfth[24]+ (record
r8f:R81+, e = 1)

The pair part of the pairing from its two integer sums and the pair self sum. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The pair part equals the pair self part of the target. -/
theorem wR8fR81p_hp : pairSumQ true wR8fR81pL wR8fR81pW = wR8fR81pW.sden * (selfPairsZ wR8fR81pW :
    ℚ) := by
  rw [pairSumQ_of_chk true wR8fR81pL wR8fR81pW (srcRootEightMatZc.act wR8fR81pH)
      (srcRootEightMat_act_entryZc wR8fR81pH) wR8fR81p_pchk, wR8fR81p_ps]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
