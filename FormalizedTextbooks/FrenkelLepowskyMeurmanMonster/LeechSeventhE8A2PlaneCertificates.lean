/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2PlaneData

/-! Ordinary-kernel finite checks for the original E8 root-plane data and source orbit. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

set_option maxHeartbeats 4000000 in
-- Check the three increasing original root addresses of every candidate plane.
/-- Each candidate has three distinct, increasingly ordered original short-line addresses. -/
theorem leechSeventhE8A2_indices_sorted : ∀ p : Fin 1120,
    leechSeventhE8A2Indices p 0 < leechSeventhE8A2Indices p 1 ∧
      leechSeventhE8A2Indices p 1 < leechSeventhE8A2Indices p 2 := by
  decide +kernel

set_option maxHeartbeats 20000000 in
-- Check all eight coordinates of every oriented three-root relation.
/-- The third root of each candidate is the checked signed sum of its first two roots. -/
theorem leechSeventhE8A2_third_relation : ∀ p : Fin 1120, ∀ i : Fin 8,
    leechSeventhE8RootLocal (leechSeventhE8A2Indices p 2) i =
      leechSeventhE8A2ThirdCoefficients p 0 *
        leechSeventhE8RootLocal (leechSeventhE8A2Indices p 0) i +
      leechSeventhE8A2ThirdCoefficients p 1 *
        leechSeventhE8RootLocal (leechSeventhE8A2Indices p 1) i := by
  decide +kernel

set_option maxHeartbeats 20000000 in
-- Test all 14400 ordered root pairs against the finite candidate lookup.
/-- Every actual nonorthogonal root pair occurs together in its indicated candidate. -/
theorem leechSeventhE8A2_pair_lookup : ∀ r s : Fin 120,
    |∑ i, leechSeventhE8RootLocal r i * leechSeventhE8RootLocal s i| = 16 →
      (∃ j : Fin 3, leechSeventhE8A2Indices (leechSeventhE8A2PairIndex r s) j = r) ∧
        (∃ j : Fin 3, leechSeventhE8A2Indices (leechSeventhE8A2PairIndex r s) j = s) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check that each noninitial orbit parent really is earlier in the finite tree.
/-- The original-generator parent graph is a well-founded finite rooted tree. -/
theorem leechSeventhE8A2_orbit_parent_lt : ∀ p : Fin 1120,
    p ≠ 0 → leechSeventhE8A2OrbitParent p < p := by
  decide +kernel

set_option maxHeartbeats 12000000 in
-- Compare both directions of each three-element original-generator image set.
/-- Every proposed parent edge is the exact action of its original section generator. -/
theorem leechSeventhE8A2_orbit_edge : ∀ p : Fin 1120, p ≠ 0 →
    (Finset.univ.image (fun j : Fin 3 => leechSeventhE8RootImage
      (leechSeventhE8A2OrbitLetter p)
      (leechSeventhE8A2Indices
        (leechSeventhE8A2OrbitIndex (leechSeventhE8A2OrbitParent p)) j))) =
      Finset.univ.image (leechSeventhE8A2Indices (leechSeventhE8A2OrbitIndex p)) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
