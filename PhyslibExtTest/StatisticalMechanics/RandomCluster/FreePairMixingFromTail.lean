/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.FreePairMixingFromTail

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.FreePairMixingFromTail`

In `ℤ²` at `p = 1/2` (`q = 2`):
* `freeAxisTranslationPower_eq_pow` at `n = 3`;
* `freeInfiniteVolume_axisShift_ergodic`: the unit axis shift is ergodic for the free measure;
* `freeInfiniteVolume_pairMixing_q2`: the free measure satisfies pair mixing.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.FreePairMixingFromTail

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice

-- The `n`-th axis translation is the `n`-th power of the unit one.
example : freeAxisTranslationPower (d := 2) one_le_two 3 = freeAxisTranslation one_le_two ^ 3 :=
  freeAxisTranslationPower_eq_pow one_le_two 3

-- The unit axis shift is ergodic for the free FK-Ising measure on `ℤ²`.
example := freeInfiniteVolume_axisShift_ergodic (d := 2) one_le_two (p := 1 / 2) (by norm_num)
  (by norm_num)

-- Pair mixing of the free FK-Ising measure on `ℤ²`.
example := freeInfiniteVolume_pairMixing_q2 (d := 2) one_le_two (p := 1 / 2) (by norm_num)
  (by norm_num)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.FreePairMixingFromTail
