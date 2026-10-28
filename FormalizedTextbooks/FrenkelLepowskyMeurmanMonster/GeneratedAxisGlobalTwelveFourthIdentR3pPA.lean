/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR3pChecks

/-! # The Fourth identification `R3p` (Twelfth target): denominators and octad packing

Part of the exact pairing `pairTriGMO` of the two representations of
`GeneratedAxisGlobalTwelveFourthIdentR3pChecks`, evaluated in its own kernel checks (one module
per memory-heavy part). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false
/-- The denominators of the two packed tensors. -/
theorem fourthR3p_dens :
    tensorWordDenAll fourthR3pH = 256 ∧
      (tensorWordDenAll fourthR3pG : ℚ) * fourthR3pSD = 8192 := by
  refine ⟨by decide, ?_⟩
  have h : tensorWordDenAll fourthR3pG = 256 := by decide
  rw [h]
  unfold fourthR3pSD
  norm_num

set_option maxRecDepth 100000 in
/-- The short scales of the two representations. -/
theorem fourthR3p_sdens : fourthR3pL.sden = 1 / 8 ∧ fourthR3pW.sden = 1 / 128 := by
  constructor
  · rfl
  · decide +kernel

set_option maxRecDepth 100000 in
/-- The octad terms of the source representation fit the packed octad transform. -/
theorem fourthR3p_octok : octPackOk 32 fourthR3pL = true := by
  decide +kernel

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
