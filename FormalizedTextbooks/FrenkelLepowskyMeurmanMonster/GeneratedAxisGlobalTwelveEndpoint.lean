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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFifthFamily
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOrderAssembly

/-! The exact remaining inputs of the global axis count, after the closed First and Odd
coverage, the five closed Fifth bindings, and the eleven closed local lengths.

The remaining inputs are: the Tenth stabilizer order; coverage of the nine families
Octad, Fourth, Sixth, Seventh, Eighth, Ninth, Root8, Twelfth and Tenth; and the sixteen
open Fifth transition vectors. These are hypotheses, not closed results. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The nine families whose triality coverage is not yet closed. -/
def generatedAxisGlobalTwelveOpenFamilies : Finset (Fin 12) :=
  {1, 3, 5, 6, 7, 8, 9, 10, 11}

/-- The global axis count from the Tenth order, nine family coverages and Fifth vectors. -/
theorem generatedAxisGlobalTwelve_axis_card_of_open
    (htenth : Nat.card (MulAction.stabilizer H generatedTenthAxis) = 2903040)
    (hcov : ∀ i ∈ generatedAxisGlobalTwelveOpenFamilies, GeneratedAxisGlobalTwelveFamilyCovered i)
    (hpos : ∀ i ∈ generatedAxisGlobalTwelveFifthOpenPositive,
      sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord i) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hneg : ∀ i ∈ generatedAxisGlobalTwelveFifthOpenNegative,
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalFifthShortLocalWord i) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (p : Fin 276) :
    Nat.card (generatedVectorOrbit (conwayShortAxis (Sum.inl (0, p)) 0)) =
      97239461142009186000 := by
  apply generatedAxisGlobalTwelve_axis_card (generatedAxisGlobalTwelveCounted_of_tenth htenth)
  intro i
  fin_cases i
  · exact generatedAxisGlobalTwelve_first_covered
  · exact hcov 1 (by decide)
  · exact generatedAxisGlobalTwelve_odd_covered
  · exact hcov 3 (by decide)
  · exact generatedAxisGlobalTwelve_fifth_covered_of hpos hneg
  · exact hcov 5 (by decide)
  · exact hcov 6 (by decide)
  · exact hcov 7 (by decide)
  · exact hcov 8 (by decide)
  · exact hcov 9 (by decide)
  · exact hcov 10 (by decide)
  · exact hcov 11 (by decide)

/-- The Monster order from these remaining global inputs and the feasible count. -/
theorem generatedAxisGlobalTwelve_order_of_open
    (htenth : Nat.card (MulAction.stabilizer H generatedTenthAxis) = 2903040)
    (hcov : ∀ i ∈ generatedAxisGlobalTwelveOpenFamilies, GeneratedAxisGlobalTwelveFamilyCovered i)
    (hpos : ∀ i ∈ generatedAxisGlobalTwelveFifthOpenPositive,
      sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord i) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hneg : ∀ i ∈ generatedAxisGlobalTwelveFifthOpenNegative,
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalFifthShortLocalWord i) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (p : Fin 276)
    (hfeasible : Nat.card (generatedFeasibleVectorOrbit (conwayShortAxis (Sum.inl (0, p)) 0)
      (conwayShortAxis (Sum.inl (0, p)) 1)) = 11707448673375) :
    Nat.card G =
      2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3 *
      17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71 :=
  generated_order_of_actual_axis_counts p
    (generatedAxisGlobalTwelve_axis_card_of_open htenth hcov hpos hneg p) hfeasible

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
