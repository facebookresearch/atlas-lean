/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR14pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcSeventhF

/-! # The Fourth identification `R14p` (Seventh target): matrix part

Part of the exact pairing `pairTriGMO` of the two representations of
`GeneratedAxisGlobalTwelveFourthIdentR14pChecks`, evaluated in its own kernel checks (one module
per memory-heavy part). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing (integer matrix block of the Seventh source). -/
theorem fourthR14p_pmat : triMatF true fourthR14pL fourthR14pW = 385 / 128 := by
  have h : ∀ i j : Fin 24, fourthR14pW.mat.entry i j = (srcSeventhMatZ.act fourthR14pG).entry i j :=
    fun i j => srcSeventhMat_act_entryZ fourthR14pG i j
  unfold triMatF
  simp only [h]
  decide +kernel

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
