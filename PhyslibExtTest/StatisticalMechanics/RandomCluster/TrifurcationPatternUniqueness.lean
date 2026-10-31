/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TrifurcationPatternUniqueness

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TrifurcationPatternUniqueness`

In `ℤ²` at `p = 1/2`:
* `wiredInfinite_q2_canonical_uniqueness`: almost surely at most one infinite cluster for the wired
  FK-Ising limit;
* `wiredInfinite_trifurcation_pos_of_top_pos` (`q = 1`) and
  `freeInfinite_trifurcation_pos_of_top_pos` (`q = 2`) in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TrifurcationPatternUniqueness

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice

-- At most one infinite cluster under the wired `q = 2` limit.
example := (wiredInfinite_q2_canonical_uniqueness (d := 2) one_le_two (p := 1 / 2) (by norm_num)
  (by norm_num)).2.2

-- Infinitely many infinite clusters would force trifurcations (wired, `q = 1`).
example := fun htop => wiredInfinite_trifurcation_pos_of_top_pos (d := 2) (p := 1 / 2) (q := 1)
  (by norm_num) (by norm_num) le_rfl htop

-- The same for the free limit at `q = 2`.
example := fun htop => freeInfinite_trifurcation_pos_of_top_pos (d := 2) (p := 1 / 2) (q := 2)
  (by norm_num) (by norm_num) one_le_two htop

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TrifurcationPatternUniqueness
