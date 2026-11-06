/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN3pXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (octad check, matrix, pairs) of the identification Ninth[5]+ <-> Twelfth[31]+
(record gninth:N3+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGninthN3pX_hm : triMatF true wGninthN3pXL wGninthN3pXW = selfMatQ wGninthN3pXW := by
  rw [triMatF_eq_ZI true wGninthN3pXL wGninthN3pXW (srcNinthMatZc.act wGninthN3pXH)
      (twelfthSrcMatZ.act wGninthN3pXG)
    (srcNinthMat_act_entryZc wGninthN3pXH) (twelfthSrcMat_act_entryZ wGninthN3pXG),
    selfMatQ_eq_ZI wGninthN3pXW (twelfthSrcMatZ.act wGninthN3pXG) (twelfthSrcMat_act_entryZ
        wGninthN3pXG)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part equals the pair self part of the target. -/
theorem wGninthN3pX_hp : pairSumQ true wGninthN3pXL wGninthN3pXW = wGninthN3pXW.sden * (selfPairsZ
    wGninthN3pXW : ℚ) := by
  rw [pairSumQ_eq_ZI true wGninthN3pXL wGninthN3pXW (srcNinthMatZc.act wGninthN3pXH)
      (srcNinthMat_act_entryZc wGninthN3pXH)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
