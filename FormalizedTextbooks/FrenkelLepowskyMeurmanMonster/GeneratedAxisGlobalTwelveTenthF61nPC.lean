/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthF61nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Pairing parts (odd short terms of the source, tensor) of the Tenth identification T61-
    (gtenth) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 0. -/
theorem tf61n_hb0 : oddLZT 64 false tf61nGX (OctadDense.octChunkTerms tf61nHC0) = 14124 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 1. -/
theorem tf61n_hb1 : oddLZT 64 false tf61nGX (OctadDense.octChunkTerms tf61nHC1) = 14762 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 2. -/
theorem tf61n_hb2 : oddLZT 64 false tf61nGX (OctadDense.octChunkTerms tf61nHC2) = 16406 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 3. -/
theorem tf61n_hb3 : oddLZT 64 false tf61nGX (OctadDense.octChunkTerms tf61nHC3) = 12052 := by
  decide +kernel

/-- The odd part `oddLZ` of the pairing (sum of the chunk groups). -/
theorem tf61n_hb : oddLZ 64 false tf61nGX tf61nL = 14124 + 14762 + 16406 + 12052 := by
  rw [oddLZ_ofList 64 false tf61nGX tf61nL tf61nHT rfl]
  simp only [tf61nHT, tf61nHC, octChunkTerms_append, oddLZT_append, tf61n_hb0, tf61n_hb1,
      tf61n_hb2, tf61n_hb3]

set_option maxRecDepth 100000 in
/-- The tensor part of the pairing. -/
theorem tf61n_hc : tdotM 64 (trialityTensorT 64 (!false) tf61nHX) tf61nGX = 114688 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
