/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationCount

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationCount`

* instance: in `tfc_lineConfig` every site is a trifurcation (`tfc_line_isTrifurcation`), and
  `Tcount` equals the volume (`tfc_line_Tcount`);
* refutations: `tfc_line_not_distinctArmEnds`, `tfc_not_forall_distinctArmEnds`,
  `tfc_not_forall_Tcount_le_boundary` in `ℤ¹`;
* non-vacuity: `tfc_DistinctArmEnds` holds for the all-closed configuration
  (`tfc_distinctArmEnds_of_subsingleton`), and `tfc_Tcount_le_boundary_of_distinctArmEnds` applies;
* `tfc_Tcount_zero_le_boundary_iff`: at `n = 0` the bound holds exactly when the origin is not a
  trifurcation; it fails for the line configuration.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationCount

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation
open _root_.StatMech.ConfigSpace MeasureTheory

variable {d : ℕ}

/-- In the all-closed configuration every open cluster is a single site. -/
theorem cluster_closed (x : Site d) : cluster d (fun _ => false) x = {x} := by
  have hbot : openSubgraph d (fun _ => false) = ⊥ := by
    ext a b
    simp
  ext y
  simp only [mem_cluster, Connected, hbot, SimpleGraph.reachable_bot, Set.mem_singleton_iff]
  exact eq_comm

/-- In the all-closed configuration no site is a trifurcation. -/
theorem not_isTrifurcation_closed (x : Site d) :
    ¬ IsTrifurcation d (fun _ => false) x := by
  rintro ⟨a₁, -, -, -, -, ⟨h, -, -⟩, -⟩
  rw [cluster_closed] at h
  exact h (Set.finite_singleton a₁)

-- Every site of the line configuration is a trifurcation.
example (x : Site 2) : IsTrifurcation 2 (tfc_lineConfig 0) x := tfc_line_isTrifurcation 0 x

-- Its trifurcation count is the volume.
example (n : ℕ) : Tcount 2 (tfc_lineConfig 0) n = (boxFinsetBK 2 n).card := tfc_line_Tcount 0 n

-- Distinct arm ends fail for the line configuration, and hence configuration-wide.
example : ¬ tfc_DistinctArmEnds (tfc_lineConfig (0 : Fin 1)) 1 ∧
    ¬ (∀ (ω : ConfigSpace (Sym2 (Site 1))) (n : ℕ), 1 ≤ n → tfc_DistinctArmEnds ω n) ∧
    ¬ (∀ (ω : ConfigSpace (Sym2 (Site 1))) (n : ℕ), 1 ≤ n →
      Tcount 1 ω n ≤ boxSV_boundaryCard 1 n) :=
  ⟨tfc_line_not_distinctArmEnds 0 le_rfl, tfc_not_forall_distinctArmEnds le_rfl,
    tfc_not_forall_Tcount_le_boundary le_rfl⟩

/-- The all-closed configuration has distinct arm ends. -/
theorem closed_cert (n : ℕ) (hn : 1 ≤ n) : tfc_DistinctArmEnds (d := d) (fun _ => false) n :=
  tfc_distinctArmEnds_of_subsingleton _ n hn fun x _ _ hx => absurd hx (not_isTrifurcation_closed x)

-- The counting bound for the witness.
example (n : ℕ) (hn : 1 ≤ n) : Tcount d (fun _ => false) n ≤ boxSV_boundaryCard d n :=
  tfc_Tcount_le_boundary_of_distinctArmEnds _ n (closed_cert n hn)

-- At `n = 0` the bound holds iff the origin is not a trifurcation: true when all is closed,
-- false for the line configuration.
example : Tcount d (fun _ => false) 0 ≤ boxSV_boundaryCard d 0 ∧
    ¬ Tcount 2 (tfc_lineConfig 0) 0 ≤ boxSV_boundaryCard 2 0 :=
  ⟨(tfc_Tcount_zero_le_boundary_iff _).mpr (not_isTrifurcation_closed 0),
    fun h => (tfc_Tcount_zero_le_boundary_iff _).mp h (tfc_line_isTrifurcation 0 0)⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationCount
