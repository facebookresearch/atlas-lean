/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.TripleBranchSelection

/-!
# Tests for `Sheffield.TripleBranchSelection`

Module under test: `Sheffield.TripleBranchSelection` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

* `tendsto_three_max_one_fixedBranches_subsequence` on explicit sequences: three pairs whose
  first member is `0` and second member is `1`, so all pair maxima are `1`.
* `NormalTwoRotatedEndpointLimitData.exists_fixedBranchesSubsequence` elaborates (check-only).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace TripleBranchSelection

open _root_.StatMech.FK.PeriodicPlanar Filter

/-- The maximum of the constant sequences `0` and `1` tends to `1`. -/
theorem max_zero_one_tendsto :
    Tendsto (fun n : ℕ => max ((fun _ => (0 : ℝ)) n) ((fun _ => (1 : ℝ)) n)) atTop (nhds 1) := by
  simp

-- A common subsequence with fixed branches for three `0`/`1` pairs.
example : ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ hB vB kB : Bool,
    Tendsto (fun n => if hB then (fun _ => (1 : ℝ)) (phi n) else (fun _ => 0) (phi n))
      atTop (nhds 1) ∧
    Tendsto (fun n => if vB then (fun _ => (1 : ℝ)) (phi n) else (fun _ => 0) (phi n))
      atTop (nhds 1) ∧
    Tendsto (fun n => if kB then (fun _ => (1 : ℝ)) (phi n) else (fun _ => 0) (phi n))
      atTop (nhds 1) :=
  tendsto_three_max_one_fixedBranches_subsequence _ _ _ _ _ _
    max_zero_one_tendsto max_zero_one_tendsto max_zero_one_tendsto

-- `NormalTwoRotatedEndpointLimitData.exists_fixedBranchesSubsequence` elaborates.
example := @NormalTwoRotatedEndpointLimitData.exists_fixedBranchesSubsequence

end TripleBranchSelection
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
