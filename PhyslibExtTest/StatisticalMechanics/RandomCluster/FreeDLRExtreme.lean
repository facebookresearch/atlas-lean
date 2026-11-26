/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.FreeDLRExtreme

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.FreeDLRExtreme`

In `ℤ²` at `p = 1/2`, `q = 2`:
* `isClopen_dependsOn_finset` for the clopen event `univ`;
* `freeInfiniteVolume_le_isFKDLR_clopen` with the free measure itself as the FK-DLR measure (its
  FK-DLR property from `freeInfiniteVolume_isFKDLR`);
* `freeInfiniteVolume_weakDLR_extreme` for the trivial decomposition `φ = ½ φ + ½ φ`;
* `freeInfinite_canonical_uniqueness_of_isErgodic` in conditional form (given ergodicity).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.FreeDLRExtreme

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice MeasureTheory

/-- The free infinite-volume measure on `ℤ²` at `p = 1/2`, `q = 2`. -/
noncomputable abbrev φ : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2))) :=
  freeInfiniteVolume 2 (p := 1 / 2) (q := 2) (by norm_num) (by norm_num) two_pos

/-- `φ` is an FK-DLR measure. -/
theorem φ_isFKDLR : IsFKDLR 2 (1 / 2) 2 φ :=
  freeInfiniteVolume_isFKDLR (by norm_num) (by norm_num) one_le_two

-- A clopen event depends on finitely many edges.
example : ∃ F : Finset (Sym2 (Site 2)),
    StatMech.DependsOn (Set.univ : Set (ConfigSpace (Sym2 (Site 2)))) (F : Set (Sym2 (Site 2))) :=
  isClopen_dependsOn_finset _ isClopen_univ

-- The free measure is dominated by an FK-DLR measure on clopen increasing events.
example := freeInfiniteVolume_le_isFKDLR_clopen (p := 1 / 2) (q := 2) (by norm_num)
  (by norm_num) one_le_two φ φ_isFKDLR

-- Extremality, applied to the trivial decomposition of the free measure.
example := freeInfiniteVolume_weakDLR_extreme (p := 1 / 2) (q := 2) (by norm_num)
  (by norm_num) one_le_two φ φ φ_isFKDLR φ_isFKDLR 2⁻¹ 2⁻¹ (by norm_num) (by norm_num)
  ENNReal.inv_two_add_inv_two (by rw [← add_smul, ENNReal.inv_two_add_inv_two, one_smul])

-- Given ergodicity, there is almost surely at most one infinite cluster.
example := fun herg => (freeInfinite_canonical_uniqueness_of_isErgodic (d := 2) one_le_two
  (p := 1 / 2) (q := 2) (by norm_num) (by norm_num) one_le_two herg).2.2

end PhyslibExtTest.StatisticalMechanics.RandomCluster.FreeDLRExtreme
