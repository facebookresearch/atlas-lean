/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineForestCount

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineForestCount`

* `bgt_genuineForest_of_noTrif` builds `bgt_GenuineForest` in the all-closed configuration of
  `ℤ` (non-vacuity), and `bgt_genuineTcount_le_boundary` applies to it.
* The third conjunct of `bgt_status`: `bc60_upperLines` has no classical coarse trifurcation.
* `bgt_genuineTcount_le_leafCard` as a conditional statement.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineForestCount

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

/-- The site `1` of `ℤ` lies on the boundary of `B_1`. -/
theorem one_mem_vertexBoundary : (fun _ => 1 : Site 1) ∈ vertexBoundary 1 1 :=
  ⟨fun _ => le_rfl, fun h => by simpa using h 0⟩

/-- The site `-1` of `ℤ` lies on the boundary of `B_1`. -/
theorem neg_one_mem_vertexBoundary : (fun _ => -1 : Site 1) ∈ vertexBoundary 1 1 :=
  ⟨fun _ => by simp, fun h => by simpa using h 0⟩

/-- The two boundary sites `1` and `-1` of `B_1 ⊂ ℤ` are distinct. -/
theorem one_ne_neg_one : (fun _ => 1 : Site 1) ≠ fun _ => -1 := fun h => by
  simpa using congrFun h 0

/-- The all-closed configuration has no classical coarse trifurcation: no edge leaves a box. -/
theorem not_genuineCoarseTrif_closed {d L : ℕ} (y : Site d) :
    ¬ btr_IsGenuineCoarseTrif (d := d) (fun _ => false) L y := by
  rintro ⟨a₁, -, -, ⟨b, -, hb⟩, -⟩
  simp at hb

/-- The classical coarse forest certificate holds in the all-closed configuration of `ℤ`. -/
theorem closed_genuineForest (L : ℕ) : bgt_GenuineForest (d := 1) (fun _ => false) L 1 :=
  bgt_genuineForest_of_noTrif _ L 1 one_mem_vertexBoundary neg_one_mem_vertexBoundary
    one_ne_neg_one fun y _ => not_genuineCoarseTrif_closed y

-- The counting bound in the all-closed configuration.
example : (btr_genuineTrifFinset (d := 1) (fun _ => false) 3 1).card ≤ boxSV_boundaryCard 1 1 :=
  bgt_genuineTcount_le_boundary _ 3 1 (closed_genuineForest 3)

-- The upper-lines configuration has no classical coarse trifurcation in any box.
example : (btr_genuineTrifFinset bc60_upperLines 3 5).card = 0 :=
  (bgt_status (d := 2) (by norm_num)).2.2.1 3 5

-- The leaf-count bound, as a conditional.
example (ω : ConfigSpace (Sym2 (Site 2))) (L R m : ℕ) (h : bgt_GenuineForestNoBnd ω L R m) :
    (btr_genuineTrifFinset ω L R).card ≤ m :=
  bgt_genuineTcount_le_leafCard ω L R m h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineForestCount
