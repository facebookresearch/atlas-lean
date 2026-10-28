/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientT4Assembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientRootEightZero
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthZero

/-! The Monster order of the generated group from the coverage predicates of families 3 to 11.

The orthogonal signed-short axis counts of the Root8 and Tenth representatives are discharged
by `GeneratedFeasibleAmbientRootEightZero` and `GeneratedFeasibleAmbientTenthZero`; the only
remaining hypotheses are the nine family coverage predicates, none of which is asserted. They are
taken either as one predicate over the indices 3 to 11 or as nine separate hypotheses. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The Monster order of the generated group from the coverage of families 3 to 11 only. -/
theorem generatedFeasibleAmbientT4_order_of_coverage
    (hcov : ∀ i ∈ ({3, 4, 5, 6, 7, 8, 9, 10, 11} : Finset (Fin 12)),
      GeneratedAxisGlobalTwelveFamilyCovered i) :
    Nat.card ↥G =
      2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3 *
      17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71 :=
  generatedFeasibleAmbientT4_order hcov generatedFeasibleAmbientAxisZeroCount_rootEight_le
    generatedFeasibleAmbientAxisZeroCount_tenth.le

/-- The Monster order of the generated group from the nine open family coverages, one explicit
hypothesis per family: Fourth, Fifth, Sixth, Seventh, Eighth, Ninth, Root8, Twelfth and Tenth
(catalogue indices 3 to 11). Each family closure theorem can be supplied by name. -/
theorem generatedFeasibleAmbientT4_order_of_families
    (hfourth : GeneratedAxisGlobalTwelveFamilyCovered 3)
    (hfifth : GeneratedAxisGlobalTwelveFamilyCovered 4)
    (hsixth : GeneratedAxisGlobalTwelveFamilyCovered 5)
    (hseventh : GeneratedAxisGlobalTwelveFamilyCovered 6)
    (heighth : GeneratedAxisGlobalTwelveFamilyCovered 7)
    (hninth : GeneratedAxisGlobalTwelveFamilyCovered 8)
    (hrootEight : GeneratedAxisGlobalTwelveFamilyCovered 9)
    (htwelfth : GeneratedAxisGlobalTwelveFamilyCovered 10)
    (htenth : GeneratedAxisGlobalTwelveFamilyCovered 11) :
    Nat.card ↥G =
      2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3 *
      17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71 := by
  refine generatedFeasibleAmbientT4_order_of_coverage fun i hi => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [hfourth, hfifth, hsixth, hseventh, heighth, hninth, hrootEight, htwelfth, htenth]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
