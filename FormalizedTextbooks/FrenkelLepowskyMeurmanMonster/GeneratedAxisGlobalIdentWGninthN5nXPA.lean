/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN5nXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM

/-! # Factory parts (octad check, matrix, pairs) of the identification Ninth[7]- <-> Ninth[7]-
(record gninth:N5-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGninthN5nX_hm : triMatF false wGninthN5nXL wGninthN5nXW = selfMatQ wGninthN5nXW := by
  rw [triMatF_eq_ZI false wGninthN5nXL wGninthN5nXW (srcNinthMatZc.act wGninthN5nXH)
      (srcNinthMatZc.act wGninthN5nXG)
    (srcNinthMat_act_entryZc wGninthN5nXH) (srcNinthMat_act_entryZc wGninthN5nXG),
    selfMatQ_eq_ZI wGninthN5nXW (srcNinthMatZc.act wGninthN5nXG) (srcNinthMat_act_entryZc
        wGninthN5nXG)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part equals the pair self part of the target. -/
theorem wGninthN5nX_hp : pairSumQ false wGninthN5nXL wGninthN5nXW = wGninthN5nXW.sden *
    (selfPairsZ wGninthN5nXW : ℚ) := by
  rw [pairSumQ_eq_ZI false wGninthN5nXL wGninthN5nXW (srcNinthMatZc.act wGninthN5nXH)
      (srcNinthMat_act_entryZc wGninthN5nXH)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
