/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.FarLeftWalk
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.FarLeftWalk`

* `fcc_xLowerBound` for a two-point set.
* `fcc_far_reach_off_finite` for the single site `{(0, 0)}`: the far-left column exists, and from
  `(-5, 7)` (if left of it) one reaches `(-9, 7)` avoiding the site.
-/

@[expose] public section

open StatMech.Lattice SimpleGraph

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.FarLeftWalk

example : ∃ b : ℤ, ∀ q ∈ ({![0, 0], ![3, -1]} : Set (Site 2)), b ≤ q 0 :=
  fcc_xLowerBound _ (Set.toFinite _)

example : ∃ b : ℤ, (∀ q ∈ ({![0, 0]} : Set (Site 2)), b ≤ q 0) ∧
      ∀ z : Site 2, z 0 ≤ b - 1 → ∀ M : ℤ, M ≤ z 0 →
        ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
          (∀ w ∈ p.support, w ∉ ({![0, 0]} : Set (Site 2))) ∧
          (∀ q ∈ ({![0, 0]} : Set (Site 2)), z0 0 ≤ q 0) ∧ z0 = ![M, z 1] :=
  fcc_far_reach_off_finite _ (Set.finite_singleton _)

/-- The far-left column for the origin is nonpositive. -/
example : ∀ b : ℤ, (∀ q ∈ ({![0, 0]} : Set (Site 2)), b ≤ q 0) → b ≤ 0 := by
  intro b hb
  simpa using hb ![0, 0] rfl

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.FarLeftWalk
