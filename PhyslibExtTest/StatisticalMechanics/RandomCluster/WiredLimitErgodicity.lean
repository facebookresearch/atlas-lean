/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.WiredLimitErgodicity

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.WiredLimitErgodicity`

In `ℤ²` at `p = 1/2` (`q = 2`):
* `feu_wiredIV_isErgodic`: the wired limit is translation-ergodic;
* `feu_wiredIV_extreme_on_invariants` for the trivial decomposition `φ = ½ φ + ½ φ` and the
  invariant event `univ`;
* `feu_fk_limits_of_freeErg` in conditional form (given free ergodicity): the free limit lies
  below the wired limit on box events.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.WiredLimitErgodicity

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice MeasureTheory

-- The wired `q = 2` limit is ergodic.
example := feu_wiredIV_isErgodic (d := 2) one_le_two (p := 1 / 2) (by norm_num) (by norm_num)

/-- The wired `q = 2` limit on `ℤ²` at `p = 1/2`, as a measure. -/
noncomputable abbrev φ : Measure (ConfigSpace (Sym2 (Site 2))) :=
  wiredInfiniteVolume 2 (p := 1 / 2) (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 2)

-- Convex summands of the wired limit agree on invariant events.
example : φ Set.univ = φ Set.univ :=
  feu_wiredIV_extreme_on_invariants one_le_two (p := 1 / 2) (by norm_num) (by norm_num) φ φ 2⁻¹ 2⁻¹
    (by norm_num) (by norm_num) (by rw [← add_smul, ENNReal.inv_two_add_inv_two, one_smul])
    MeasurableSet.univ fun _ => Set.preimage_univ

-- Given free ergodicity, the free limit lies below the wired one on box events.
example := fun hFreeErg => (feu_fk_limits_of_freeErg 2 one_le_two (p := 1 / 2) (by norm_num)
  (by norm_num) hFreeErg).2.2.2.2.2.2 0 isUpperSet_univ

end PhyslibExtTest.StatisticalMechanics.RandomCluster.WiredLimitErgodicity
