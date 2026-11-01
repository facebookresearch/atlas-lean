/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN4nXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octad check, matrix, pairs) of the identification Ninth[6]- <-> Tenth[74]-
(record gninth:N4-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGninthN4nX_hm : triMatF false wGninthN4nXL wGninthN4nXW = selfMatQ wGninthN4nXW := by
  rw [triMatF_eq_ZI false wGninthN4nXL wGninthN4nXW (srcNinthMatZc.act wGninthN4nXH)
      (srcTenthMatZc.act wGninthN4nXG)
    (srcNinthMat_act_entryZc wGninthN4nXH) (srcTenthMat_act_entryZc wGninthN4nXG),
    selfMatQ_eq_ZI wGninthN4nXW (srcTenthMatZc.act wGninthN4nXG) (srcTenthMat_act_entryZc
        wGninthN4nXG)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part equals the pair self part of the target. -/
theorem wGninthN4nX_hp : pairSumQ false wGninthN4nXL wGninthN4nXW = wGninthN4nXW.sden *
    (selfPairsZ wGninthN4nXW : ℚ) := by
  rw [pairSumQ_eq_ZI false wGninthN4nXL wGninthN4nXW (srcNinthMatZc.act wGninthN4nXH)
      (srcNinthMat_act_entryZc wGninthN4nXH)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
