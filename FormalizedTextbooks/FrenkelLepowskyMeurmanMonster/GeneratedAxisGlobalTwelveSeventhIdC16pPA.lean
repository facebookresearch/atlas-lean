/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC16pLW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Parts (octad check, matrix, pairs) of the identification Seventh cell record S7c16+
(gforest:S7c16+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
    /-- The octad terms of the source representation fit the packed octad transform. -/
    theorem s7c16p_hok : octPackOk 40 s7c16pL = true := by decide +kernel

    set_option maxRecDepth 100000 in
    /-- The matrix part equals the matrix self part of the target. -/
    theorem s7c16p_hm : triMatF true s7c16pL s7c16pW = selfMatQ s7c16pW := by
      rw [triMatF_eq_ZI true s7c16pL s7c16pW (srcSeventhMatZ.act s7c16pH) (srcRootEightMatZc.act
          s7c16pG)
        (srcSeventhMat_act_entryZ s7c16pH) (srcRootEightMat_act_entryZc s7c16pG),
        selfMatQ_eq_ZI s7c16pW (srcRootEightMatZc.act s7c16pG) (srcRootEightMat_act_entryZc
            s7c16pG)]
      decide +kernel

    set_option maxRecDepth 100000 in
    /-- The pair part equals the pair self part of the target. -/
    theorem s7c16p_hp : pairSumQ true s7c16pL s7c16pW = s7c16pW.sden * (selfPairsZ s7c16pW : ℚ) :=
        by
      rw [pairSumQ_eq_ZI true s7c16pL s7c16pW (srcSeventhMatZ.act s7c16pH)
          (srcSeventhMat_act_entryZ s7c16pH)]
      decide +kernel

    end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
