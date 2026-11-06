/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN7nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ

/-! # Factory parts (octad check, matrix, pairs) of the identification Fifth[4]+ <-> Ninth[12]-
(record gninth:N7-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGninthN7n_hm : triMatF false wGninthN7nL wGninthN7nW = selfMatQ wGninthN7nW := by
  rw [triMatF_eq_ZI false wGninthN7nL wGninthN7nW (srcNinthMatZc.act wGninthN7nH)
      (fifthSrcMatZ.act wGninthN7nG)
    (srcNinthMat_act_entryZc wGninthN7nH) (fifthSrcMat_act_entry wGninthN7nG),
    selfMatQ_eq_ZI wGninthN7nW (fifthSrcMatZ.act wGninthN7nG) (fifthSrcMat_act_entry wGninthN7nG)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part equals the pair self part of the target. -/
theorem wGninthN7n_hp : pairSumQ false wGninthN7nL wGninthN7nW = wGninthN7nW.sden * (selfPairsZ
    wGninthN7nW : ℚ) := by
  rw [pairSumQ_eq_ZI false wGninthN7nL wGninthN7nW (srcNinthMatZc.act wGninthN7nH)
      (srcNinthMat_act_entryZc wGninthN7nH)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
