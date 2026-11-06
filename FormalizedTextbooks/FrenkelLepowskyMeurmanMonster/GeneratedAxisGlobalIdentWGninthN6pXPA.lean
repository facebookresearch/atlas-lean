/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN6pXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (octad check, matrix, pairs) of the identification Ninth[10]+ <-> Twelfth[12]-
(record gninth:N6+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGninthN6pX_hm : triMatF true wGninthN6pXL wGninthN6pXW = selfMatQ wGninthN6pXW := by
  rw [triMatF_eq_ZI true wGninthN6pXL wGninthN6pXW (srcNinthMatZc.act wGninthN6pXH)
      (twelfthSrcMatZ.act wGninthN6pXG)
    (srcNinthMat_act_entryZc wGninthN6pXH) (twelfthSrcMat_act_entryZ wGninthN6pXG),
    selfMatQ_eq_ZI wGninthN6pXW (twelfthSrcMatZ.act wGninthN6pXG) (twelfthSrcMat_act_entryZ
        wGninthN6pXG)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part equals the pair self part of the target. -/
theorem wGninthN6pX_hp : pairSumQ true wGninthN6pXL wGninthN6pXW = wGninthN6pXW.sden * (selfPairsZ
    wGninthN6pXW : ℚ) := by
  rw [pairSumQ_eq_ZI true wGninthN6pXL wGninthN6pXW (srcNinthMatZc.act wGninthN6pXH)
      (srcNinthMat_act_entryZc wGninthN6pXH)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
