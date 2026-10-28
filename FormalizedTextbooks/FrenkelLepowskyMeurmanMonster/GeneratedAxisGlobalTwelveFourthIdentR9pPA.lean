/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR9pChecks

/-! # The Fourth identification `R9p` (Eighth target): denominators and octad packing

Part of the exact pairing `pairTriGMO` of the two representations of
`GeneratedAxisGlobalTwelveFourthIdentR9pChecks`, evaluated in its own kernel checks (one module
per memory-heavy part). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false
/-- The denominators of the two packed tensors. -/
theorem fourthR9p_dens :
    tensorWordDenAll fourthR9pH = 256 ∧
      (tensorWordDenAll fourthR9pG : ℚ) * fourthR9pSD = 4194304 := by
  refine ⟨by decide, ?_⟩
  have h : tensorWordDenAll fourthR9pG = 512 := by decide
  rw [h]
  unfold fourthR9pSD
  rw [srcEighthH_den]
  norm_num

set_option maxRecDepth 100000 in
/-- The short scales of the two representations. -/
theorem fourthR9p_sdens : fourthR9pL.sden = 1 / 8 ∧ fourthR9pW.sden = 1 / 8192 := by
  constructor
  · rfl
  · decide +kernel

set_option maxRecDepth 100000 in
/-- The octad terms of the source representation fit the packed octad transform. -/
theorem fourthR9p_octok : octPackOk 32 fourthR9pL = true := by
  decide +kernel

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
