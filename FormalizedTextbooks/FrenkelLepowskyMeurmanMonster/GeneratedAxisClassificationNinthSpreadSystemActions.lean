/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadSystemCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsOrbitBasis

/-! All compact system transitions are actions of the genuine section isometries on whole actual
lattice-quotient subspaces. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Every transition is the entire original lattice-quotient subspace action. -/
theorem generatedNinth_spread_system_action (g : Fin 18) (k : Fin 270) :
    generatedAxisE8FrameSystemOrbitLetter g • generatedAxisE8ActualFrameSystemCandidate k =
      generatedAxisE8ActualFrameSystemCandidate (generatedNinthSpreadSystemTarget g k) := by
  exact generatedNinth_spread_system_action_of_labels g k
    (fun j => generatedNinth_spread_system_label_image g k j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
