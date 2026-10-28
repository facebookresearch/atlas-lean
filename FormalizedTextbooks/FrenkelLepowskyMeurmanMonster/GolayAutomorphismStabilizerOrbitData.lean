/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismStabilizerData

/-! Prefix and orbit coverage certificates for the actual stabilizer arrays. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Permissible images of the next base point at each level. -/
def golayStabilizerOrbitEligible (k : Fin 7) (i : Fin 24) : Prop :=
  if k.val < 5 then k.val ≤ i.val
  else if k.val = 5 then 8 ≤ i.val
  else i = 5 ∨ i = 6 ∨ i = 7

instance (k : Fin 7) (i : Fin 24) : Decidable (golayStabilizerOrbitEligible k i) := by
  unfold golayStabilizerOrbitEligible
  infer_instance

set_option maxHeartbeats 4000000 in
-- Every representative fixes all preceding base points.
theorem golayStabilizerRep_prefix_certificate : ∀ r : Fin 129, ∀ j : Fin 7,
    j.val < (golayStabilizerRepLevel r).val →
      golayStabilizerRepForward r (golayBasePoints j) = golayBasePoints j := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Representatives cover every eligible next-point image at all seven levels.
theorem golayStabilizerRep_orbit_certificate : ∀ k : Fin 7, ∀ i : Fin 24,
    golayStabilizerOrbitEligible k i → ∃ r : Fin 129,
      golayStabilizerRepLevel r = k ∧ golayStabilizerRepForward r (golayBasePoints k) = i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
