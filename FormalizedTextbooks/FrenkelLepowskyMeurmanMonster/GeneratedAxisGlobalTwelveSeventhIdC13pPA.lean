/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC13pLW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ

/-! # Parts (octad check, matrix, pairs) of the identification Seventh cell record S7c13+
(gforest:S7c13+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
    /-- The octad terms of the source representation fit the packed octad transform. -/
    theorem s7c13p_hok : octPackOk 40 s7c13pL = true := by decide +kernel

    set_option maxRecDepth 100000 in
    /-- The matrix part equals the matrix self part of the target. -/
    theorem s7c13p_hm : triMatF true s7c13pL s7c13pW = selfMatQ s7c13pW := by
      rw [triMatF_eq_ZI true s7c13pL s7c13pW (srcSeventhMatZ.act s7c13pH) (srcSeventhMatZ.act
          s7c13pG)
        (srcSeventhMat_act_entryZ s7c13pH) (srcSeventhMat_act_entryZ s7c13pG),
        selfMatQ_eq_ZI s7c13pW (srcSeventhMatZ.act s7c13pG) (srcSeventhMat_act_entryZ s7c13pG)]
      decide +kernel

    set_option maxRecDepth 100000 in
    /-- The pair part equals the pair self part of the target. -/
    theorem s7c13p_hp : pairSumQ true s7c13pL s7c13pW = s7c13pW.sden * (selfPairsZ s7c13pW : ℚ) :=
        by
      rw [pairSumQ_eq_ZI true s7c13pL s7c13pW (srcSeventhMatZ.act s7c13pH)
          (srcSeventhMat_act_entryZ s7c13pH)]
      decide +kernel

    end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
