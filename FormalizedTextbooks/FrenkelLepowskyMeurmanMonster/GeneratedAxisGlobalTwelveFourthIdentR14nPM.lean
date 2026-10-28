/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR14nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixth

/-! # The Fourth identification `R14n` (Sixth target): matrix part

Part of the exact pairing `pairTriGMO` of the two representations of
`GeneratedAxisGlobalTwelveFourthIdentR14nChecks`, evaluated in its own kernel checks (one module
per memory-heavy part). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing (integer matrix block of the Sixth source). -/
theorem fourthR14n_pmat : triMatF false fourthR14nL fourthR14nW = 497 / 128 := by
  have h : ∀ i j : Fin 24, fourthR14nW.mat.entry i j = (sixthSrcMatZ.act fourthR14nG).entry i j :=
    fun i j => sixthSrcMat_act_entryZ fourthR14nG i j
  unfold triMatF
  simp only [h]
  decide +kernel

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
