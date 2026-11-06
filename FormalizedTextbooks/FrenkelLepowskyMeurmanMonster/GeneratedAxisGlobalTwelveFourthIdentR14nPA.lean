/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR14nChecks

/-! # The Fourth identification `R14n` (Sixth target): denominators and octad packing

Part of the exact pairing `pairTriGMO` of the two representations of
`GeneratedAxisGlobalTwelveFourthIdentR14nChecks`, evaluated in its own kernel checks (one module
per memory-heavy part). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false
/-- The denominators of the two packed tensors. -/
theorem fourthR14n_dens :
    tensorWordDenAll fourthR14nH = 256 ∧
      (tensorWordDenAll fourthR14nG : ℚ) * fourthR14nSD = 16384 := by
  refine ⟨by decide, ?_⟩
  have h : tensorWordDenAll fourthR14nG = 512 := by decide
  rw [h]
  unfold fourthR14nSD
  norm_num

set_option maxRecDepth 100000 in
/-- The short scales of the two representations. -/
theorem fourthR14n_sdens : fourthR14nL.sden = 1 / 8 ∧ fourthR14nW.sden = 1 / 32 := by
  constructor
  · rfl
  · decide +kernel

set_option maxRecDepth 100000 in
/-- The octad terms of the source representation fit the packed octad transform. -/
theorem fourthR14n_octok : octPackOk 32 fourthR14nL = true := by
  decide +kernel

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
