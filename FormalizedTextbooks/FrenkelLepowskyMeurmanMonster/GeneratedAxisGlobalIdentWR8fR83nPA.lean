/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR83nPAm
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR83nPAp1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR83nPAp2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR83nPAp3

/-! # Factory parts (matrix, pairs) of the identification Root8[11]- <-> Twelfth[29]- (record
r8f:R83-, e = -1)

The pair part of the pairing from its two integer sums and the pair self sum. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The pair part equals the pair self part of the target. -/
theorem wR8fR83n_hp : pairSumQ false wR8fR83nL wR8fR83nW = wR8fR83nW.sden * (selfPairsZ wR8fR83nW
    : ℚ) := by
  have hd : (srcRootEightMatZc.act wR8fR83nH).den = 16 := by decide +kernel
  have hk : (srcRootEightMatZc.act wR8fR83nH).k = 2 := by decide +kernel
  rw [pairSumQ_eq_ZI false wR8fR83nL wR8fR83nW (srcRootEightMatZc.act wR8fR83nH)
      (srcRootEightMat_act_entryZc wR8fR83nH), pairSumZI_eq, wR8fR83n_pm, wR8fR83n_pl,
    wR8fR83n_ps, hd, hk]
  norm_num [wR8fR83nL, wR8fR83nW]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
