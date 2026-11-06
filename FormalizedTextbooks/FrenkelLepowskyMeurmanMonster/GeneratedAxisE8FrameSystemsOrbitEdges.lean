/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsOrbitData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsOrbitBasis

/-! Each finite parent edge is the full original action on an actual frame system. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Each checked parent edge acts on the entire genuine quotient subspace. -/
theorem generatedAxisE8FrameSystemOrbit_edge_actual (k : Fin 2) (i : Fin 135) :
    generatedAxisE8FrameSystemOrbitLetter
        (generatedAxisE8FrameSystemOrbitGenerator k i) •
      generatedAxisE8ActualFrameSystemCandidate (generatedAxisE8FrameSystemOrbitIndex k
        (generatedAxisE8FrameSystemOrbitParent k i)) =
      generatedAxisE8ActualFrameSystemCandidate (generatedAxisE8FrameSystemOrbitIndex k i) := by
  apply generatedAxisE8ActualFrameSystemCandidate_action_eq_of_basis
  intro j
  dsimp only [generatedAxisE8FrameSystemOrbitLetter]
  rw [generatedFifthSectionGenerator_binary, generatedAxisE8FrameSystemOrbit_edge_certificate]
  exact Submodule.mem_map.mpr ⟨_, ⟨generatedAxisE8FrameSystemOrbitCoefficient k i j, rfl⟩, rfl⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
