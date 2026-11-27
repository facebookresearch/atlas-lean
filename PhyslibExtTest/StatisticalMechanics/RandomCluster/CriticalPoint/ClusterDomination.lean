/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.ClusterDomination

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.ClusterDomination`

In `ℤ²`, with `S = {0}` inside `box 2 0` and `p = 0` (where `φ_p(S) = 0 < 1`, a satisfiable
instance of the finite-volume criterion):
* `crossProb_geometricTail` and `clusterSizeMoment_lt_top` apply;
* `clusterRadiusDomination` packages the crossing tail, with `dist` the crossing probability;
* `geometricTail_of_expDecay` for `f n = exp (-n)`;
* `clusterSizeLargeEvent_subset_crossing` (unconditional).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.ClusterDomination

open _root_.StatMech _root_.StatMech.BeffaraDC _root_.StatMech.Percolation
open _root_.StatMech.Lattice
open scoped NNReal

/-- The criterion `φ_0({0}) < 1` holds. -/
theorem phi_zero_lt_one : phi 2 0 zero_le_one ({origin 2} : Finset (Site 2)) < 1 := by
  simp [phi]

/-- The origin lies in `{0}`. -/
theorem origin_mem : origin 2 ∈ ((({origin 2} : Finset (Site 2))) : Set (Site 2)) := by simp

/-- `{0}` lies in `box 2 0`. -/
theorem singleton_sub_box : (({origin 2} : Finset (Site 2)) : Set (Site 2)) ⊆ box 2 (1 - 1) := by
  intro x hx
  simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx
  subst hx
  simp [origin]

-- The crossing probability has a geometric tail.
example := crossProb_geometricTail 0 zero_le_one {origin 2} origin_mem phi_zero_lt_one 1 le_rfl
  singleton_sub_box

-- The radius domination has the crossing probability as its distribution.
example : (clusterRadiusDomination 0 zero_le_one {origin 2} origin_mem phi_zero_lt_one 1 le_rfl
    singleton_sub_box).dist = fun n => crossProb 2 0 zero_le_one n := rfl

-- All moments of the cluster size are finite.
example := clusterSizeMoment_lt_top 0 zero_le_one {origin 2} origin_mem phi_zero_lt_one 1 le_rfl
  singleton_sub_box 3

-- Exponential decay gives a geometric tail.
example : ∃ r, 0 < r ∧ r < 1 ∧ ∀ n : ℕ, Real.exp (-1 * n) ≤ 1 * r ^ n :=
  geometricTail_of_expDecay one_pos (fun n => by rw [one_mul])

-- Large clusters cross.
example (n : ℕ) : clusterSizeLargeEvent 2 n ⊆ crossingEvent 2 n :=
  clusterSizeLargeEvent_subset_crossing n

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.ClusterDomination
