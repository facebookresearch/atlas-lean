/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsExact
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsMaximal

/-! Every intrinsic sixteen-element singular space is maximal, using the checked
candidate cover and the independently checked adjoining-vector obstructions. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A totally singular subspace containing a genuine intrinsic four-space equals it. -/
theorem generatedAxisE8IntrinsicFrameSystems_maximal
    (V W : Submodule (ZMod 2) (Fin 8 → ZMod 2))
    (hV : V ∈ generatedAxisE8IntrinsicFrameSystems) (hVW : V ≤ W)
    (hW : ∀ v ∈ W, generatedAxisE8FrameQuadratic v = 0) : W = V := by
  obtain ⟨k, rfl⟩ := generatedAxisE8FrameSystems_complete V hV
  exact generatedAxisE8FrameSystemCandidate_maximal k W hVW hW

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
