/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineBoxOpenForest

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineBoxOpenForest`

* `bc90_genuineTrif_iff_canonical` on the upper-lines configuration at the origin.
* The last conjunct of `bc90_status`: `bc60_upperLines` has no classical trifurcation in `B_n`.
* `bc90_genuineTcount_le_boundary_of_genuine_armsInBox` in the all-closed configuration of `ℤ²`,
  where both hypotheses hold vacuously (non-vacuity of the conditional).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineBoxOpenForest

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

/-- In the all-closed configuration every cluster is a single site, so no site is a
trifurcation. -/
theorem not_isTrifurcation_closed {d : ℕ} (x : Site d) :
    ¬ IsTrifurcation d (fun _ => false) x := by
  rintro ⟨a, -, -, -, -, ⟨h, -, -⟩, -⟩
  have hb : openSubgraph d (fun _ => false) = ⊥ := by ext; simp
  have hc : cluster d (fun _ => false) a = {a} := by
    ext y
    simp [cluster, Connected, hb, eq_comm]
  exact h (hc ▸ Set.finite_singleton a)

-- Classical and canonical trifurcations agree.
example : bc89_GenuineTrif 2 bc60_upperLines 0 ↔ IsCanonicalTrifurcation 2 bc60_upperLines 0 :=
  bc90_genuineTrif_iff_canonical _ _

-- The upper-lines configuration has no classical trifurcation in `B_4`.
example : bc89_genuineTcount bc60_upperLines 4 = 0 :=
  (bc90_status.2.2.2.2.2 4).1

-- The classical count bound in the all-closed configuration.
example : bc89_genuineTcount (d := 2) (fun _ => false) 2 ≤ boxSV_boundaryCard 2 2 :=
  bc90_genuineTcount_le_boundary_of_genuine_armsInBox _ 2 (by norm_num)
    (fun x _ hx => absurd hx (not_isTrifurcation_closed x))
    (fun x _ hx => absurd hx (not_isTrifurcation_closed x))

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineBoxOpenForest
