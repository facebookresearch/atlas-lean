/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinCompactConjugation

/-! Complete actual binary images of genuine compact orthogonal spin products. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Compare every complete compact generator image on all twenty-four original Q coordinates.
/-- The genuine compact product's entire binary columns match their retained exact data. -/
theorem generatedTwelfth_spin_compact_binary_certificate : ∀ (g : Fin 12) (j : Fin 24),
    toAdd (qQuotHom (generatedTwelfthSpinCompactQImage g (qCoordinateGenerator j))) =
      monsterCo1GeometryBinaryMaskDecode (generatedTwelfthSpinCompactBinaryColumns g j) := by
  decide +kernel

/-- Packed single bits are exactly the original twenty-four positive coordinate vectors. -/
theorem generatedTwelfth_spin_compact_binary_basis : ∀ j : Fin 24,
    monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val) = Pi.single j 1 := by
  decide +kernel

/-- Each actual compact spin binary column is the genuine full original coordinate image. -/
theorem generatedTwelfth_spin_compact_binary_generator_actual (g : Fin 12) (j : Fin 24) :
    spinBinaryAction (generatedTwelfthSpinCompact g)
        (monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val)) =
      monsterCo1GeometryBinaryMaskDecode (generatedTwelfthSpinCompactBinaryColumns g j) := by
  rw [generatedTwelfth_spin_compact_binary_basis]
  change qBinaryAction (spinConjugation (generatedTwelfthSpinCompact g))
    (toAdd (qQuotHom (qCoordinateGenerator j))) = _
  rw [qBinaryAction_apply, generatedTwelfth_spin_compact_conjugation,
    generatedTwelfth_spin_compact_binary_certificate]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
