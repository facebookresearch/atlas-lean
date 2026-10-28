/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2PlaneData

/-! Exact integral Gram operators for the original finite A2 root triples. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

set_option maxHeartbeats 12000000 in
-- Check all signs in the original oriented three-root relations.
/-- Both coefficients of every oriented third-root relation are actual unit signs. -/
theorem leechSeventhE8A2_third_coefficient_sign : ∀ p : Fin 1120, ∀ j : Fin 2,
    leechSeventhE8A2ThirdCoefficients p j = 1 ∨
      leechSeventhE8A2ThirdCoefficients p j = -1 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Evaluate the 1120 original first-pair inner products on eight integral coordinates.
/-- Every candidate is spanned by an actual nonorthogonal root pair. -/
theorem leechSeventhE8A2_first_pair : ∀ p : Fin 1120,
    |∑ i, leechSeventhE8RootLocal (leechSeventhE8A2Indices p 0) i *
      leechSeventhE8RootLocal (leechSeventhE8A2Indices p 1) i| = 16 := by
  decide +kernel

set_option maxHeartbeats 40000000 in
-- Check all 26880 coordinates of the three-root integral Gram eigenvalue identities.
/-- The original integral root outer sum acts by forty-eight on all three generating roots. -/
theorem leechSeventhE8A2_root_gram : ∀ p : Fin 1120, ∀ k : Fin 3, ∀ i : Fin 8,
    (∑ j : Fin 3, (∑ l : Fin 8,
      leechSeventhE8RootLocal (leechSeventhE8A2Indices p j) l *
        leechSeventhE8RootLocal (leechSeventhE8A2Indices p k) l) *
      leechSeventhE8RootLocal (leechSeventhE8A2Indices p j) i) =
        48 * leechSeventhE8RootLocal (leechSeventhE8A2Indices p k) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
