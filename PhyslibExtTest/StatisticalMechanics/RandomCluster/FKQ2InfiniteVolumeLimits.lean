/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.FKQ2InfiniteVolumeLimits

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.FKQ2InfiniteVolumeLimits`

* `fk_q2_infiniteVolume_limits` in conditional form on `ℤ²` at `p = 1/2`: given the two
  extremality hypotheses, the free and wired limits are ordered on the sure box event, and both
  limits are translation invariant.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.FKQ2InfiniteVolumeLimits

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice

-- Given extremality, the free limit lies below the wired limit on box events.
example := fun hW hF =>
  (fk_q2_infiniteVolume_limits 2 one_le_two (p := 1 / 2) (by norm_num) (by norm_num) hW
    hF).2.2.2.2.2.2 0 isUpperSet_univ

-- Given extremality, both limits are translation invariant.
example := fun hW hF =>
  let h := fk_q2_infiniteVolume_limits 2 one_le_two (p := 1 / 2) (by norm_num) (by norm_num)
    hW hF
  And.intro h.2.2.1 h.2.2.2.1

end PhyslibExtTest.StatisticalMechanics.RandomCluster.FKQ2InfiniteVolumeLimits
