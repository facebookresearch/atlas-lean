/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN2nXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octad check, matrix, pairs) of the identification Ninth[3]- <-> Tenth[50]+
(record gninth:N2-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGninthN2nX_hm : triMatF false wGninthN2nXL wGninthN2nXW = selfMatQ wGninthN2nXW := by
  rw [triMatF_eq_ZI false wGninthN2nXL wGninthN2nXW (srcNinthMatZc.act wGninthN2nXH)
      (srcTenthMatZc.act wGninthN2nXG)
    (srcNinthMat_act_entryZc wGninthN2nXH) (srcTenthMat_act_entryZc wGninthN2nXG),
    selfMatQ_eq_ZI wGninthN2nXW (srcTenthMatZc.act wGninthN2nXG) (srcTenthMat_act_entryZc
        wGninthN2nXG)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part equals the pair self part of the target. -/
theorem wGninthN2nX_hp : pairSumQ false wGninthN2nXL wGninthN2nXW = wGninthN2nXW.sden *
    (selfPairsZ wGninthN2nXW : ℚ) := by
  rw [pairSumQ_eq_ZI false wGninthN2nXL wGninthN2nXW (srcNinthMatZc.act wGninthN2nXH)
      (srcNinthMat_act_entryZc wGninthN2nXH)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
