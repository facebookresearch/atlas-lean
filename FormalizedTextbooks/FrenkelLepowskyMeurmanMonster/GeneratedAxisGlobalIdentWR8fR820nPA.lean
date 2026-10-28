/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR820nPAm
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR820nPAp1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR820nPAp2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR820nPAp3

/-! # Factory parts (matrix, pairs) of the identification Root8[25]- <-> Root8[25]- (record
r8f:R820-, e = -1)

The pair part of the pairing from its two integer sums and the pair self sum. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The pair part equals the pair self part of the target. -/
theorem wR8fR820n_hp : pairSumQ false wR8fR820nL wR8fR820nW = wR8fR820nW.sden * (selfPairsZ
    wR8fR820nW : ℚ) := by
  have hd : (srcRootEightMatZ.act wR8fR820nH).den = 16 := by decide +kernel
  have hk : (srcRootEightMatZ.act wR8fR820nH).k = 1 := by decide +kernel
  rw [pairSumQ_eq_ZI false wR8fR820nL wR8fR820nW (srcRootEightMatZ.act wR8fR820nH)
      (srcRootEightMat_act_entryZ wR8fR820nH), pairSumZI_eq, wR8fR820n_pm, wR8fR820n_pl,
    wR8fR820n_ps, hd, hk]
  norm_num [wR8fR820nL, wR8fR820nW]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
