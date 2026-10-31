/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalArmSubforest

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalArmSubforest`

* The third conjunct of `bfin_status` builds `bau_ArmSubforestData` in the all-closed
  configuration of `ℤ²`, which has no contracted-lattice trifurcation (non-vacuity); the fourth
  conjunct then gives the coarse counting bound.
* The second conjunct of `bfin_status`: a subgraph of the empty graph is acyclic (instance).
* The first conjunct as a conditional statement.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalArmSubforest

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls
open scoped NNReal

/-- Every cluster of the all-closed configuration is finite. -/
theorem cluster_closed_finite {d : ℕ} (a : Site d) : (cluster d (fun _ => false) a).Finite := by
  have hb : openSubgraph d (fun _ => false) = ⊥ := by ext; simp
  have hc : cluster d (fun _ => false) a = {a} := by
    ext y
    simp [cluster, Connected, hb, eq_comm]
  exact hc ▸ Set.finite_singleton a

/-- Removing sites from the all-closed configuration changes nothing. -/
theorem removeSites_closed {d : ℕ} (T : Finset (Site d)) :
    removeSites T (fun _ => false) = fun _ => false :=
  funext fun e => by unfold removeSites; split_ifs <;> rfl

/-- The all-closed configuration has no contracted-lattice trifurcation. -/
theorem not_gnTrif_closed {d L : ℕ} (y : Site d) :
    ¬ bc67_IsGnTrifurcation (d := d) (fun _ => false) L y := by
  rintro ⟨a₁, -, -, -, ⟨h, -, -⟩, -⟩
  rw [removeSites_closed] at h
  exact h (cluster_closed_finite a₁)

/-- Arm-subforest data in the all-closed configuration. -/
theorem closed_armSubforestData (L : ℕ) : bau_ArmSubforestData (fun _ => false) L 1 :=
  bfin_status.2.2.1 _ L 1 le_rfl fun y _ => not_gnTrif_closed y

-- The coarse counting bound in the all-closed configuration.
example : bc61_coarseTcount (d := 2) (fun _ => false) 3 1 ≤ boxSV_boundaryCard 2 1 :=
  bfin_status.2.2.2 _ 3 1 (closed_armSubforestData 3)

-- Subgraphs of acyclic graphs are acyclic.
example : (⊥ : SimpleGraph (Fin 3)).IsAcyclic :=
  bfin_status.2.1 SimpleGraph.isAcyclic_bot le_rfl

-- The configuration-wide data would rule out two infinite clusters.
example (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  bfin_status.1 p hp1 hp0 h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalArmSubforest
