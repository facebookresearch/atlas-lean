/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR820nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcRootEightCF

/-! # Factory parts (matrix) of the identification Root8[25]- <-> Root8[25]- (record r8f:R820-, e
= -1)

Dense pair blocks: the pair part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false


set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wR8fR820n_hm : triMatF false wR8fR820nL wR8fR820nW = selfMatQ wR8fR820nW := by
  rw [triMatF_eq_ZI false wR8fR820nL wR8fR820nW (srcRootEightMatZ.act wR8fR820nH)
      (srcRootEightMatZ.act wR8fR820nG)
    (srcRootEightMat_act_entryZ wR8fR820nH) (srcRootEightMat_act_entryZ wR8fR820nG),
    selfMatQ_eq_ZI wR8fR820nW (srcRootEightMatZ.act wR8fR820nG) (srcRootEightMat_act_entryZ
        wR8fR820nG)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
