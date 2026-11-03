/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.CoherentLimit

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.CoherentLimit`

On the square lattice `square` at `p = 1/2`, `q = 1`:
* `bufferedRadius` starts at `0` and dominates the index (`id_le_bufferedRadius` at `3`);
* `freeBufferedMeasure_step_cylinder` compares boxes `0` and `1` on the increasing event "every
  edge of the buffered box `0` is open";
* `freeBufferedMeasure_weakConverges` and `wiredBufferedMeasure_weakConverges` apply to `square`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.CoherentLimit

open MeasureTheory _root_.StatMech _root_.StatMech.FK.PeriodicPlanar

-- The buffered radius starts at `0`.
example : square.bufferedRadius 0 = 0 := square.bufferedRadius_zero

-- The buffered radius dominates the index.
example : 3 ≤ square.bufferedRadius 3 := square.id_le_bufferedRadius 3

/-- The event that every edge of the buffered box `0` is open. -/
def allOpenBox : Set (ConfigSpace (Sym2 (square.BufferedVertex 0))) := {ψ | ∀ e, ψ e = true}

/-- `allOpenBox` is increasing. -/
theorem allOpenBox_isIncreasing : IsIncreasing allOpenBox := by
  intro x y hxy hx e
  have h := hxy e
  rw [hx e] at h
  exact top_le_iff.mp h

-- The free buffered measure increases from box `0` to box `1` on `allOpenBox`.
example :
    (square.freeBufferedMeasure 0 (p := 1 / 2) (q := 1) (by norm_num) (by norm_num)
        (zero_lt_one.trans_le le_rfl) : Measure _).real (square.bufferedCylinder 0 allOpenBox) ≤
      (square.freeBufferedMeasure 1 (p := 1 / 2) (q := 1) (by norm_num) (by norm_num)
        (zero_lt_one.trans_le le_rfl) : Measure _).real (square.bufferedCylinder 0 allOpenBox) :=
  square.freeBufferedMeasure_step_cylinder le_rfl _ _ le_rfl allOpenBox_isIncreasing

-- The free buffered measures on `square` converge weakly.
example : WeakConvergesTo
    (fun n => square.freeBufferedMeasure n (p := 1 / 2) (q := 1) (by norm_num) (by norm_num)
      (zero_lt_one.trans_le le_rfl))
    (square.freeBufferedInfiniteVolume (p := 1 / 2) (q := 1) (by norm_num) (by norm_num)
      (zero_lt_one.trans_le le_rfl)) :=
  square.freeBufferedMeasure_weakConverges _ _ le_rfl

-- The wired buffered measures on `square` converge weakly.
example : WeakConvergesTo
    (fun n => square.wiredBufferedMeasure n (p := 1 / 2) (q := 1) (by norm_num) (by norm_num)
      (zero_lt_one.trans_le le_rfl))
    (square.wiredBufferedInfiniteVolume (p := 1 / 2) (q := 1) (by norm_num) (by norm_num)
      (zero_lt_one.trans_le le_rfl)) :=
  square.wiredBufferedMeasure_weakConverges _ _ le_rfl

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.CoherentLimit
