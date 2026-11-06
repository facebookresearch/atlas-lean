/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c12pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Factory parts (octad check, matrix, pairs) of the identification Root8[10]- <-> Seventh[19]+
(record gforest:S7c12+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGforestS7c12p_hm : triMatF true wGforestS7c12pL wGforestS7c12pW = selfMatQ
    wGforestS7c12pW := by
  rw [triMatF_eq_ZI true wGforestS7c12pL wGforestS7c12pW (srcSeventhMatZ.act wGforestS7c12pH)
      (srcRootEightMatZc.act wGforestS7c12pG)
    (srcSeventhMat_act_entryZ wGforestS7c12pH) (srcRootEightMat_act_entryZc wGforestS7c12pG),
    selfMatQ_eq_ZI wGforestS7c12pW (srcRootEightMatZc.act wGforestS7c12pG)
        (srcRootEightMat_act_entryZc wGforestS7c12pG)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part equals the pair self part of the target. -/
theorem wGforestS7c12p_hp : pairSumQ true wGforestS7c12pL wGforestS7c12pW = wGforestS7c12pW.sden *
    (selfPairsZ wGforestS7c12pW : ℚ) := by
  rw [pairSumQ_eq_ZI true wGforestS7c12pL wGforestS7c12pW (srcSeventhMatZ.act wGforestS7c12pH)
      (srcSeventhMat_act_entryZ wGforestS7c12pH)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
