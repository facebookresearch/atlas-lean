/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR821nwPAm
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR821nwPAp
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR821nwPAp3

/-! # Factory parts (matrix, pairs) of the identification Root8[33]- <-> Root8[33]- (record
r8f:R821-, e = -1)

The pair part of the pairing from its two integer sums and the pair self sum. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The pair part equals the pair self part of the target. -/
theorem wR8fR821nw_hp : pairSumQ false wR8fR821nwL wR8fR821nwW = wR8fR821nwW.sden * (selfPairsZ
    wR8fR821nwW : ℚ) := by
  rw [pairSumQ_of_chk false wR8fR821nwL wR8fR821nwW (srcRootEightMatZc.act wR8fR821nwH)
      (srcRootEightMat_act_entryZc wR8fR821nwH) wR8fR821nw_pchk, wR8fR821nw_ps]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
