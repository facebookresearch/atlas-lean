/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR6pChecks

/-! # The Fourth identification `R6p` (Seventh target): denominators and octad packing

Part of the exact pairing `pairTriGMO` of the two representations of
`GeneratedAxisGlobalTwelveFourthIdentR6pChecks`, evaluated in its own kernel checks (one module
per memory-heavy part). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false
/-- The denominators of the two packed tensors. -/
theorem fourthR6p_dens :
    tensorWordDenAll fourthR6pH = 256 ∧
      (tensorWordDenAll fourthR6pG : ℚ) * fourthR6pSD = 4194304 := by
  refine ⟨by decide, ?_⟩
  have h : tensorWordDenAll fourthR6pG = 512 := by decide
  rw [h]
  unfold fourthR6pSD
  rw [srcSeventhH_den]
  norm_num

set_option maxRecDepth 100000 in
/-- The short scales of the two representations. -/
theorem fourthR6p_sdens : fourthR6pL.sden = 1 / 8 ∧ fourthR6pW.sden = 1 / 8192 := by
  constructor
  · rfl
  · decide +kernel

set_option maxRecDepth 100000 in
/-- The octad terms of the source representation fit the packed octad transform. -/
theorem fourthR6p_octok : octPackOk 32 fourthR6pL = true := by
  decide +kernel

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
