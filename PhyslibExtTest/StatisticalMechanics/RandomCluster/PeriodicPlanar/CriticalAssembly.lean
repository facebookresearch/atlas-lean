/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.CriticalAssembly

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.CriticalAssembly`

With the toy percolation function `θ p = max 0 (p - 1 / 2)`:
* its zero set in `(0, 1)` is `(0, 1 / 2]`, with supremum `1 / 2`;
* `offCriticalSharpness_of_nonnegative_monotoneOn` gives sharpness of `0 < θ` at `1 / 2`;
* the subcritical set of the square lattice is bounded above (`subcriticalSet_bddAbove`), and
  `wiredPercolates_of_criticalPoint_lt` applied above an assumed critical point.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.CriticalAssembly

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar Set

/-- The zero set of the toy percolation function in `(0, 1)` is `(0, 1 / 2]`. -/
theorem toy_zeroSet :
    {p : ℝ | p ∈ Ioo (0 : ℝ) 1 ∧ max 0 (p - 1 / 2) = 0} = Ioc 0 (1 / 2) := by
  ext p
  simp only [mem_ofPred_eq, mem_Ioo, mem_Ioc, max_eq_left_iff, tsub_le_iff_right, zero_add]
  constructor
  · rintro ⟨⟨h0, -⟩, h⟩
    exact ⟨h0, h⟩
  · rintro ⟨h0, h⟩
    exact ⟨⟨h0, by linarith⟩, h⟩

-- Sharpness of the toy model at `1 / 2`.
example : OffCriticalSharpness (fun p : ℝ => 0 < max 0 (p - 1 / 2)) (1 / 2) :=
  offCriticalSharpness_of_nonnegative_monotoneOn (fun _ => le_max_left _ _)
    (fun _ _ _ _ h => max_le_max le_rfl (by linarith))
    (by rw [toy_zeroSet]; exact ⟨1 / 2, by norm_num⟩)
    (by rw [toy_zeroSet, csSup_Ioc (by norm_num)])

-- The square-lattice subcritical set is bounded above.
example (q : ℝ) : BddAbove (square.subcriticalSet q) :=
  square.subcriticalSet_bddAbove q

-- Supercritical parameters percolate (conditional on the position of `pc`).
example (q : ℝ) (h : square.criticalPoint q < 1 / 2) : square.wiredPercolates (1 / 2) q :=
  square.wiredPercolates_of_criticalPoint_lt (by norm_num) h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.CriticalAssembly
