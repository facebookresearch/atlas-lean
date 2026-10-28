/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN3nXChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (octad check, matrix, pairs) of the identification Ninth[5]- <-> Twelfth[31]+
(record gninth:N3-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGninthN3nX_hm : triMatF false wGninthN3nXL wGninthN3nXW = selfMatQ wGninthN3nXW := by
  rw [triMatF_eq_ZI false wGninthN3nXL wGninthN3nXW (srcNinthMatZc.act wGninthN3nXH)
      (twelfthSrcMatZ.act wGninthN3nXG)
    (srcNinthMat_act_entryZc wGninthN3nXH) (twelfthSrcMat_act_entryZ wGninthN3nXG),
    selfMatQ_eq_ZI wGninthN3nXW (twelfthSrcMatZ.act wGninthN3nXG) (twelfthSrcMat_act_entryZ
        wGninthN3nXG)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part equals the pair self part of the target. -/
theorem wGninthN3nX_hp : pairSumQ false wGninthN3nXL wGninthN3nXW = wGninthN3nXW.sden *
    (selfPairsZ wGninthN3nXW : ℚ) := by
  rw [pairSumQ_eq_ZI false wGninthN3nXL wGninthN3nXW (srcNinthMatZc.act wGninthN3nXH)
      (srcNinthMat_act_entryZc wGninthN3nXH)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
