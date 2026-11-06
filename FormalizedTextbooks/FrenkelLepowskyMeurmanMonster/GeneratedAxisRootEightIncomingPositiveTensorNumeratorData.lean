/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingSpatialData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorCircuitReplay

/-! Complete integer numerator of every original positive incoming tensor coefficient. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The entire eight-factor incoming numerator, including all original zero coefficients. -/
def generatedRootEightIncomingPositiveTensorNumerator (n : Fin 4096) (i : Fin 24) : ℤ :=
  ∑ r : Fin 8, generatedRootEightIncomingTensorSpinInteger r n *
    generatedRootEightIncomingSpatialNumerator r i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
