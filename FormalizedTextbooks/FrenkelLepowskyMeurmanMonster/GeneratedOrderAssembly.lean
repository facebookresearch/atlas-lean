/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisPairCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderExact

/-! Final arithmetic assembly from the two actual global orbit counts.
The global counts are explicit remaining hypotheses, not constructed sets of prescribed size. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The genuine global pair stabilizer has the exact source order. -/
theorem generatedShortAxisPairStabilizer_card_exact (p : Fin 276) :
    Nat.card (generatedShortAxisPairStabilizer p) = 709767191322427392000 := by
  rw [generatedShortAxisPairStabilizer_card_relation, co2Short_card_exact]
  norm_num

/-- The two actual orbit enumerations suffice for the Monster order, using the
proved genuine lattice order and genuine global common stabilizer. -/
theorem generated_order_of_actual_axis_counts (p : Fin 276)
    (haxis : Nat.card (generatedVectorOrbit (conwayShortAxis (Sum.inl (0, p)) 0)) =
      97239461142009186000)
    (hfeasible : Nat.card (generatedFeasibleVectorOrbit (conwayShortAxis (Sum.inl (0, p)) 0)
      (conwayShortAxis (Sum.inl (0, p)) 1)) = 11707448673375) :
    Nat.card G =
      2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3 *
      17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71 := by
  rw [generated_card_eq_actual_axis_orbits p, haxis, hfeasible, co2Short_card_exact]
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
