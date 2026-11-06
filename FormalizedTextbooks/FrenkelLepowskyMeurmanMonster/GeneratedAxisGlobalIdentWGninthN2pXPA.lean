/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN2pXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octad check, matrix, pairs) of the identification Ninth[3]+ <-> Tenth[50]+
(record gninth:N2+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGninthN2pX_hm : triMatF true wGninthN2pXL wGninthN2pXW = selfMatQ wGninthN2pXW := by
  rw [triMatF_eq_ZI true wGninthN2pXL wGninthN2pXW (srcNinthMatZc.act wGninthN2pXH)
      (srcTenthMatZc.act wGninthN2pXG)
    (srcNinthMat_act_entryZc wGninthN2pXH) (srcTenthMat_act_entryZc wGninthN2pXG),
    selfMatQ_eq_ZI wGninthN2pXW (srcTenthMatZc.act wGninthN2pXG) (srcTenthMat_act_entryZc
        wGninthN2pXG)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part equals the pair self part of the target. -/
theorem wGninthN2pX_hp : pairSumQ true wGninthN2pXL wGninthN2pXW = wGninthN2pXW.sden * (selfPairsZ
    wGninthN2pXW : ℚ) := by
  rw [pairSumQ_eq_ZI true wGninthN2pXL wGninthN2pXW (srcNinthMatZc.act wGninthN2pXH)
      (srcNinthMat_act_entryZc wGninthN2pXH)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
