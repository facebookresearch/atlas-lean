/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.FKGeneralQInfiniteFKG

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.FKGeneralQInfiniteFKG`

In `ℤ²` at `p = 1/2`, `q = 2`, for the increasing box events "the box edge `e` is open":
* `fkgq_freeFiniteMeasure_fkg` for boxes `N = 1 ≤ m = 2`;
* `fkgq_freeInfiniteVolume_fkg` for two single-edge events of the box `Λ_1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.FKGeneralQInfiniteFKG

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice

/-- "The box edge `e` is open" is an increasing box event. -/
theorem edgeOpen_isIncreasing {n : ℕ} (e : Sym2 (boxVerts 2 n)) :
    IsIncreasing {ω : ConfigSpace (Sym2 (boxVerts 2 n)) | ω e = true} := by
  intro x y hxy hx
  have h := hxy e
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

-- FKG for the finite free measure on `Λ_2`, for events of `Λ_1`.
example (e f : Sym2 (boxVerts 2 1)) :=
  fkgq_freeFiniteMeasure_fkg 1 2 (by norm_num) (p := 1 / 2) (q := 2) (by norm_num) (by norm_num)
    one_le_two (edgeOpen_isIncreasing e) (edgeOpen_isIncreasing f)

-- FKG for the free infinite-volume measure, for events of `Λ_1`.
example (e f : Sym2 (boxVerts 2 1)) :=
  fkgq_freeInfiniteVolume_fkg 1 (p := 1 / 2) (q := 2) (by norm_num) (by norm_num) one_le_two
    (edgeOpen_isIncreasing e) (edgeOpen_isIncreasing f)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.FKGeneralQInfiniteFKG
