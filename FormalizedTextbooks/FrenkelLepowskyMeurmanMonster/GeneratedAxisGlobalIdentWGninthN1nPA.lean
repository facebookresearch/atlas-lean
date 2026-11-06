/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN1nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octad check, matrix, pairs) of the identification Ninth[1]- <-> Tenth[33]+
(record gninth:N1-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGninthN1n_hm : triMatF false wGninthN1nL wGninthN1nW = selfMatQ wGninthN1nW := by
  rw [triMatF_eq_ZI false wGninthN1nL wGninthN1nW (srcNinthMatZc.act wGninthN1nH)
      (srcTenthMatZc.act wGninthN1nG)
    (srcNinthMat_act_entryZc wGninthN1nH) (srcTenthMat_act_entryZc wGninthN1nG),
    selfMatQ_eq_ZI wGninthN1nW (srcTenthMatZc.act wGninthN1nG) (srcTenthMat_act_entryZc
        wGninthN1nG)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part equals the pair self part of the target. -/
theorem wGninthN1n_hp : pairSumQ false wGninthN1nL wGninthN1nW = wGninthN1nW.sden * (selfPairsZ
    wGninthN1nW : ℚ) := by
  rw [pairSumQ_eq_ZI false wGninthN1nL wGninthN1nW (srcNinthMatZc.act wGninthN1nH)
      (srcNinthMat_act_entryZc wGninthN1nH)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
