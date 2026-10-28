/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveCounts
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFirstFamily
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOddFamily
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOrderAssembly

/-! Family-level final wrapper for the global axis count and the Monster order.

The First and Odd families are covered and eleven local lengths are closed. The remaining
inputs are the Tenth stabilizer order and the coverage predicates of the ten families
Octad, Fourth, Fifth, Sixth, Seventh, Eighth, Ninth, Root8, Twelfth and Tenth. These are
hypotheses, not closed results; each family scope targets one coverage predicate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The ten families whose coverage predicate is not yet closed. -/
def generatedAxisGlobalTwelveRemainingFamilies : Finset (Fin 12) :=
  {1, 3, 4, 5, 6, 7, 8, 9, 10, 11}

/-- The global axis count from the Tenth order and ten family coverages. -/
theorem generatedAxisGlobalTwelve_axis_card_of_families
    (htenth : Nat.card (MulAction.stabilizer H generatedTenthAxis) = 2903040)
    (hcov : ∀ i ∈ generatedAxisGlobalTwelveRemainingFamilies,
      GeneratedAxisGlobalTwelveFamilyCovered i)
    (p : Fin 276) :
    Nat.card (generatedVectorOrbit (conwayShortAxis (Sum.inl (0, p)) 0)) =
      97239461142009186000 := by
  apply generatedAxisGlobalTwelve_axis_card (generatedAxisGlobalTwelveCounted_of_tenth htenth)
  intro i
  by_cases h0 : i = 0
  · subst h0
    exact generatedAxisGlobalTwelve_first_covered
  by_cases h2 : i = 2
  · subst h2
    exact generatedAxisGlobalTwelve_odd_covered
  apply hcov i
  fin_cases i <;> simp_all [generatedAxisGlobalTwelveRemainingFamilies]

/-- The Monster order from the Tenth order, ten family coverages and the feasible count. -/
theorem generatedAxisGlobalTwelve_order_of_families
    (htenth : Nat.card (MulAction.stabilizer H generatedTenthAxis) = 2903040)
    (hcov : ∀ i ∈ generatedAxisGlobalTwelveRemainingFamilies,
      GeneratedAxisGlobalTwelveFamilyCovered i)
    (p : Fin 276)
    (hfeasible : Nat.card (generatedFeasibleVectorOrbit (conwayShortAxis (Sum.inl (0, p)) 0)
      (conwayShortAxis (Sum.inl (0, p)) 1)) = 11707448673375) :
    Nat.card G =
      2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3 *
      17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71 :=
  generated_order_of_actual_axis_counts p
    (generatedAxisGlobalTwelve_axis_card_of_families htenth hcov p) hfeasible

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
