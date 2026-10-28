/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN7nXChecks
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
theorem wGninthN7nX_hm : triMatF false wGninthN7nXL wGninthN7nXW = selfMatQ wGninthN7nXW := by
  rw [triMatF_eq_ZI false wGninthN7nXL wGninthN7nXW (srcNinthMatZc.act wGninthN7nXH)
      (fifthSrcMatZ.act wGninthN7nXG)
    (srcNinthMat_act_entryZc wGninthN7nXH) (fifthSrcMat_act_entry wGninthN7nXG),
    selfMatQ_eq_ZI wGninthN7nXW (fifthSrcMatZ.act wGninthN7nXG) (fifthSrcMat_act_entry
        wGninthN7nXG)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part equals the pair self part of the target. -/
theorem wGninthN7nX_hp : pairSumQ false wGninthN7nXL wGninthN7nXW = wGninthN7nXW.sden *
    (selfPairsZ wGninthN7nXW : ℚ) := by
  rw [pairSumQ_eq_ZI false wGninthN7nXL wGninthN7nXW (srcNinthMatZc.act wGninthN7nXH)
      (srcNinthMat_act_entryZc wGninthN7nXH)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
