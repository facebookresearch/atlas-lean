/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR7pChecks

/-! # The Fourth identification `R7p` (Seventh target): denominators and octad packing

Part of the exact pairing `pairTriGMO` of the two representations of
`GeneratedAxisGlobalTwelveFourthIdentR7pChecks`, evaluated in its own kernel checks (one module
per memory-heavy part). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false
/-- The denominators of the two packed tensors. -/
theorem fourthR7p_dens :
    tensorWordDenAll fourthR7pH = 256 ∧
      (tensorWordDenAll fourthR7pG : ℚ) * fourthR7pSD = 1073741824 := by
  refine ⟨by decide, ?_⟩
  have h : tensorWordDenAll fourthR7pG = 131072 := by decide
  rw [h]
  unfold fourthR7pSD
  rw [srcSeventhH_den]
  norm_num

set_option maxRecDepth 100000 in
/-- The short scales of the two representations. -/
theorem fourthR7p_sdens : fourthR7pL.sden = 1 / 8 ∧ fourthR7pW.sden = 1 / 8192 := by
  constructor
  · rfl
  · decide +kernel

set_option maxRecDepth 100000 in
/-- The octad terms of the source representation fit the packed octad transform. -/
theorem fourthR7p_octok : octPackOk 32 fourthR7pL = true := by
  decide +kernel

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
