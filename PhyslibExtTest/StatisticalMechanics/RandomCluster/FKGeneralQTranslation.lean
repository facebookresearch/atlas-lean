/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.FKGeneralQTranslation

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.FKGeneralQTranslation`

In `ℤ²` at `p = 1/2`, `q = 2`:
* `wiredInfiniteVolume_isTranslationInvariant` and `freeInfiniteVolume_isTranslationInvariant`;
* `fkgqt_wired_multiOpen_translation` for the single-edge set `{s(0, (1, 0))}` translated by
  `(0, 1)`;
* `measure_eq_of_multiOpen_eq` for a Dirac measure on `ConfigSpace ℕ` compared with itself.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.FKGeneralQTranslation

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice MeasureTheory

-- The wired and free infinite-volume measures are translation invariant.
example := wiredInfiniteVolume_isTranslationInvariant (d := 2) (p := 1 / 2) (q := 2)
  (by norm_num) (by norm_num) one_le_two

-- The free infinite-volume measure is translation invariant.
example := freeInfiniteVolume_isTranslationInvariant (d := 2) (p := 1 / 2) (q := 2)
  (by norm_num) (by norm_num) one_le_two

-- "The edge `s(0, (1, 0))` is open" has the same wired probability after a translation.
example := fkgqt_wired_multiOpen_translation (d := 2) (p := 1 / 2) (q := 2) ![0, 1]
  {s(0, ![1, 0])} (by norm_num) (by norm_num) one_le_two

-- Equal multi-open probabilities determine the measure.
example : (Measure.dirac (fun _ => true) : Measure (ConfigSpace ℕ)) =
    Measure.dirac (fun _ => true) :=
  measure_eq_of_multiOpen_eq _ _ fun _ => rfl

end PhyslibExtTest.StatisticalMechanics.RandomCluster.FKGeneralQTranslation
