/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixLifts

/-! Only the three genuine compatible candidates needed by the checked projection generation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- The original index of one of the three genuine generating candidates. -/
def generatedTwelfthThreeCandidateIndex (g : Fin 3) : Fin 12 :=
  ⟨g.val, by omega⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
