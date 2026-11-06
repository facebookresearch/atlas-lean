/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCompactQConjugation

/-! Complete original compact Q images at all twenty-four binary coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxHeartbeats 64000000 in
-- Evaluate all original binary coordinates and retain the entire central coefficient.
set_option maxRecDepth 100000 in
-- Expand only one compact original generator, with at most eight Fourier factors.
/-- Every original compact basis image has the full recorded binary and central coordinates. -/
theorem generatedRootEight_compact_q_basis_12 : ∀ j : Fin 24,
    generatedRootEightCompactQImage 12 (qCoordinateGenerator j) =
      generatedRootEightCompactBasisImage 12 j := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
