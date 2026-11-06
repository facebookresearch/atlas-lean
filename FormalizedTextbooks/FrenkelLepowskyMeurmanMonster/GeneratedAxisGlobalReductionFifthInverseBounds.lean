/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthInverseData
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskBounds

/-! Every compact inverse parent stays in the actual 24-coordinate mask domain. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The checked inverse action has no bits outside the genuine 24 coordinates. -/
theorem generatedAxisGlobalFifthInverseRows_lt (k : Fin 19) (b : ℕ) :
    generatedAxisGlobalMaskRowsAction (generatedAxisGlobalFifthInverseRows k) b < 2 ^ 24 := by
  apply generatedAxisGlobalMaskRowsAction_lt
  rw [(generatedAxisGlobalFifthInverse_certificate k).2]
  intro p hp
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
  exact ((generatedAxisGlobalFifthInverse_certificate k).1 j).1

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
