/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadSystemBasis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadSystemPacket00

/-! The first original section sign acts on all 270 genuine whole frame systems. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every first-letter table image is the entire original lattice-quotient subspace action. -/
theorem generatedNinth_spread_system_zero_action (k : Fin 270) :
    generatedAxisE8FrameSystemOrbitLetter 0 • generatedAxisE8ActualFrameSystemCandidate k =
      generatedAxisE8ActualFrameSystemCandidate (generatedNinthSpreadSystemTarget 0 k) :=
  generatedNinth_spread_system_action_of_labels 0 k (generatedNinth_spread_system_packet_00 k)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
