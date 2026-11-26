/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineTrifNotion

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineTrifNotion`

* `btr_bc60_not_genuineTrif` and the third conjunct of `btr_status`: the upper-lines
  configuration has no classical coarse trifurcation, so its count is `0`.
* The all-closed configuration of `ℤ` has none either: no edge leaves any box.
* `btr_genuine_imp_bc61` as a conditional statement.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineTrifNotion

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

-- The upper-lines configuration has no classical coarse trifurcation.
example : ¬ btr_IsGenuineCoarseTrif bc60_upperLines 3 0 ∧
    (btr_genuineTrifFinset bc60_upperLines 3 4).card = 0 :=
  ⟨btr_bc60_not_genuineTrif 3 0, btr_status.2.2 3 4⟩

/-- The all-closed configuration has no classical coarse trifurcation: no edge leaves a box. -/
theorem not_genuineCoarseTrif_closed {d L : ℕ} (y : Site d) :
    ¬ btr_IsGenuineCoarseTrif (d := d) (fun _ => false) L y := by
  rintro ⟨a₁, -, -, ⟨b, -, hb⟩, -⟩
  simp at hb

-- The classical coarse count of the all-closed configuration is `0`.
example : btr_genuineTrifFinset (d := 1) (fun _ => false) 2 3 = ∅ := by
  classical
  rw [btr_genuineTrifFinset, Finset.filter_eq_empty_iff]
  exact fun y _ => not_genuineCoarseTrif_closed y

-- Classical coarse trifurcations are coarse trifurcations.
example (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y : Site 2)
    (h : btr_IsGenuineCoarseTrif ω L y) : bc61_IsCoarseTrifurcation ω L y :=
  btr_genuine_imp_bc61 h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineTrifNotion
