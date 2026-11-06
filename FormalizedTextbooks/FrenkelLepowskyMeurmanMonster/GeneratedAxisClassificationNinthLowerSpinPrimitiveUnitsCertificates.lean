/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitiveUnitsFormulas

/-! Genuine full extraspecial primitive action, independent of full-word source certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

set_option maxHeartbeats 16000000 in
-- Bind all positive generator images directly to the original quadratic/Gaussian formulas.
/-- All positive primitive generator caches retain the actual original central coefficient. -/
theorem generatedNinth_lower_spin_primitive_units_positive_certificate :
    ∀ (k : Fin 15) (j : Fin 24),
      generatedNinthLowerSpinPrimitiveUnitsPositiveQImage k (qCoordinateGenerator j) =
        generatedNinthLowerSpinPrimitiveQGenerator (k, false) j := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Replay each inverse candidate through the actual positive source formula.
/-- Every inverse primitive candidate is the genuine preimage of its coordinate generator. -/
theorem generatedNinth_lower_spin_primitive_units_inverse_certificate :
    ∀ (k : Fin 15) (j : Fin 24),
      generatedNinthLowerSpinPrimitiveUnitsPositiveQImage k
        (generatedNinthLowerSpinPrimitiveQGenerator (k, true) j) = qCoordinateGenerator j := by
  decide +kernel


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
