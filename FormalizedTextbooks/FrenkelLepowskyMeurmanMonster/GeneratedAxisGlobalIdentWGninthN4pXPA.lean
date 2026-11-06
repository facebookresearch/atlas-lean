/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN4pXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octad check, matrix, pairs) of the identification Ninth[6]+ <-> Tenth[74]-
(record gninth:N4+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGninthN4pX_hm : triMatF true wGninthN4pXL wGninthN4pXW = selfMatQ wGninthN4pXW := by
  rw [triMatF_eq_ZI true wGninthN4pXL wGninthN4pXW (srcNinthMatZc.act wGninthN4pXH)
      (srcTenthMatZc.act wGninthN4pXG)
    (srcNinthMat_act_entryZc wGninthN4pXH) (srcTenthMat_act_entryZc wGninthN4pXG),
    selfMatQ_eq_ZI wGninthN4pXW (srcTenthMatZc.act wGninthN4pXG) (srcTenthMat_act_entryZc
        wGninthN4pXG)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part equals the pair self part of the target. -/
theorem wGninthN4pX_hp : pairSumQ true wGninthN4pXL wGninthN4pXW = wGninthN4pXW.sden * (selfPairsZ
    wGninthN4pXW : ℚ) := by
  rw [pairSumQ_eq_ZI true wGninthN4pXL wGninthN4pXW (srcNinthMatZc.act wGninthN4pXH)
      (srcNinthMat_act_entryZc wGninthN4pXH)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
