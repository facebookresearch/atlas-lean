/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.InfiniteFiniteEnergy

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.InfiniteFiniteEnergy`

In `ℤ²` at `p = 1/2`, `q = 2`:
* `measurable_setOpen` for an edge of `ℤ²`;
* `freeInfinite_setOpen_absolutelyContinuous`: forcing the edge `s(0, (1, 0))` open preserves
  free null sets;
* `wiredInfinite_setPattern_absolutelyContinuous` for the all-open pattern on that edge;
* `wiredInfiniteVolume_hasFiniteEnergyMerge` and `freeInfiniteVolume_hasFiniteEnergyMerge`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.InfiniteFiniteEnergy

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice

/-- The edge from the origin to `(1, 0)`. -/
def e0 : Sym2 (Site 2) := s(0, ![1, 0])

-- Forcing an edge open is measurable.
example : Measurable (setOpen e0) := measurable_setOpen e0

-- Forcing an edge open is absolutely continuous for the free measure.
example := freeInfinite_setOpen_absolutelyContinuous (d := 2) (p := 1 / 2) (q := 2)
  (by norm_num) (by norm_num) one_le_two e0

-- Forcing a finite pattern is absolutely continuous for the wired measure.
example := wiredInfinite_setPattern_absolutelyContinuous (d := 2) (p := 1 / 2) (q := 2)
  (by norm_num) (by norm_num) one_le_two {e0} (fun _ => true)

-- Both infinite-volume measures have finite-energy merging.
example := And.intro
  (wiredInfiniteVolume_hasFiniteEnergyMerge (d := 2) (p := 1 / 2) (q := 2) (by norm_num)
    (by norm_num) one_le_two)
  (freeInfiniteVolume_hasFiniteEnergyMerge (d := 2) (p := 1 / 2) (q := 2) (by norm_num)
    (by norm_num) one_le_two)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.InfiniteFiniteEnergy
