/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR813pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcRootEightCF

/-! # Factory parts (octad check, matrix, pairs) of the identification Root8[7]+ <-> Root8[7]+
(record r8f:R813+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wR8fR813p_hm : triMatF true wR8fR813pL wR8fR813pW = selfMatQ wR8fR813pW := by
  rw [triMatF_eq_ZI true wR8fR813pL wR8fR813pW (srcRootEightMatZ.act wR8fR813pH)
      (srcRootEightMatZ.act wR8fR813pG)
    (srcRootEightMat_act_entryZ wR8fR813pH) (srcRootEightMat_act_entryZ wR8fR813pG),
    selfMatQ_eq_ZI wR8fR813pW (srcRootEightMatZ.act wR8fR813pG) (srcRootEightMat_act_entryZ
        wR8fR813pG)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part equals the pair self part of the target. -/
theorem wR8fR813p_hp : pairSumQ true wR8fR813pL wR8fR813pW = wR8fR813pW.sden * (selfPairsZ
    wR8fR813pW : ℚ) := by
  rw [pairSumQ_eq_ZI true wR8fR813pL wR8fR813pW (srcRootEightMatZ.act wR8fR813pH)
      (srcRootEightMat_act_entryZ wR8fR813pH)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
