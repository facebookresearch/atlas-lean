/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.FreeTailTriviality

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.FreeTailTriviality`

In `ℤ²` at `p = 1/2`:
* `freeInfiniteVolume_tail_trivial_generalQ` in conditional form (for any tail event), `q = 1`;
* `freeInfiniteVolume_isErgodic_generalQ` at `q = 1`;
* `freeInfinite_canonical_uniqueness` at `q = 1` and `freeInfinite_q2_canonical_uniqueness`:
  almost surely at most one infinite cluster.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.FreeTailTriviality

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice

-- Tail events have free probability `0` or `1`.
example (s : Set (ConfigSpace (Sym2 (Site 2)))) (hs : FKIsTailEvent 2 s) :=
  freeInfiniteVolume_tail_trivial_generalQ (p := 1 / 2) (q := 1) (by norm_num) (by norm_num)
    le_rfl s hs

-- The free measure is translation-ergodic.
example := freeInfiniteVolume_isErgodic_generalQ (d := 2) one_le_two (p := 1 / 2) (q := 1)
  (by norm_num) (by norm_num) le_rfl

-- At most one infinite cluster, Bernoulli percolation (`q = 1`).
example := (freeInfinite_canonical_uniqueness (d := 2) one_le_two (p := 1 / 2) (q := 1)
  (by norm_num) (by norm_num) le_rfl).2.2

-- At most one infinite cluster, FK-Ising (`q = 2`).
example := (freeInfinite_q2_canonical_uniqueness (d := 2) one_le_two (p := 1 / 2)
  (by norm_num) (by norm_num)).2.1

end PhyslibExtTest.StatisticalMechanics.RandomCluster.FreeTailTriviality
