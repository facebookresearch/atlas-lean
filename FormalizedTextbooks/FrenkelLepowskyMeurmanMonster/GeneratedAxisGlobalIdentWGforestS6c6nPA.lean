/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS6c6nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWDense
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixth

/-! # Factory parts (octad check, matrix, pairs) of the identification Sixth[11]- <-> Sixth[11]-
(record gforest:S6c6-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGforestS6c6n_hm : triMatF false wGforestS6c6nL wGforestS6c6nW = selfMatQ wGforestS6c6nW
    := by
  rw [triMatF_eq_ZI false wGforestS6c6nL wGforestS6c6nW (sixthSrcMatZ.act wGforestS6c6nH)
      (sixthSrcMatZ.act wGforestS6c6nG)
    (sixthSrcMat_act_entryZ wGforestS6c6nH) (sixthSrcMat_act_entryZ wGforestS6c6nG),
    selfMatQ_eq_ZI wGforestS6c6nW (sixthSrcMatZ.act wGforestS6c6nG) (sixthSrcMat_act_entryZ
        wGforestS6c6nG)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part equals the pair self part of the target. -/
theorem wGforestS6c6n_hp : pairSumQ false wGforestS6c6nL wGforestS6c6nW = wGforestS6c6nW.sden *
    (selfPairsZ wGforestS6c6nW : ℚ) := by
  rw [pairSumQ_eq_ZI false wGforestS6c6nL wGforestS6c6nW (sixthSrcMatZ.act wGforestS6c6nH)
      (sixthSrcMat_act_entryZ wGforestS6c6nH)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
