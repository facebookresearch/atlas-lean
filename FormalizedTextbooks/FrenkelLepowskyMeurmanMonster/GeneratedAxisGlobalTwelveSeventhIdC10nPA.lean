/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC10nLW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Parts (octad check, matrix, pairs) of the identification Seventh cell record S7c10-
(gforest:S7c10-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
    /-- The octad terms of the source representation fit the packed octad transform. -/
    theorem s7c10n_hok : octPackOk 40 s7c10nL = true := by decide +kernel

    set_option maxRecDepth 100000 in
    /-- The matrix part equals the matrix self part of the target. -/
    theorem s7c10n_hm : triMatF false s7c10nL s7c10nW = selfMatQ s7c10nW := by
      rw [triMatF_eq_ZI false s7c10nL s7c10nW (srcSeventhMatZ.act s7c10nH) (srcRootEightMatZc.act
          s7c10nG)
        (srcSeventhMat_act_entryZ s7c10nH) (srcRootEightMat_act_entryZc s7c10nG),
        selfMatQ_eq_ZI s7c10nW (srcRootEightMatZc.act s7c10nG) (srcRootEightMat_act_entryZc
            s7c10nG)]
      decide +kernel

    set_option maxRecDepth 100000 in
    /-- The pair part equals the pair self part of the target. -/
    theorem s7c10n_hp : pairSumQ false s7c10nL s7c10nW = s7c10nW.sden * (selfPairsZ s7c10nW : ℚ)
        := by
      rw [pairSumQ_eq_ZI false s7c10nL s7c10nW (srcSeventhMatZ.act s7c10nH)
          (srcSeventhMat_act_entryZ s7c10nH)]
      decide +kernel

    end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
