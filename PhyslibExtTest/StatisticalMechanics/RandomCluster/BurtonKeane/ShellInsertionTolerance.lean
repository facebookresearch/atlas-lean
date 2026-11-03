/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ShellInsertionTolerance

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ShellInsertionTolerance`

* `bins_bk_atLeastTwo` in conditional form (the route package gives no two infinite clusters);
* `bins_cluster_closeTouch_eq_removeBox` applied to the all-closed configuration: after closing the
  box bonds and removing the origin, the cluster of `u` is the singleton `{u}`;
* `bins_measurable_closeI` and `bins_ExtEvent_dependsOn` applied.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ShellInsertionTolerance

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls
open _root_.StatMech.ConfigSpace MeasureTheory
open scoped NNReal
open _root_.StatMech.Ising

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

/-- Removing sites from the all-closed configuration leaves it all-closed. -/
theorem removeSites_closed (T : Finset (Site d)) :
    removeSites T (fun _ => false) = fun _ => false := by
  funext e
  simp only [removeSites, ite_self]

-- The route package excludes two infinite clusters.
example (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (hplt : p < 1) (hres : bins_Route p hp1) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  bins_bk_atLeastTwo p hp1 hp0 hplt hres

-- Closing the bonds touching `B_n` and removing the origin is removing the box.
example (n : ℕ) (u : Site 2) :
    cluster 2 (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) (fun _ => false))) u = {u} := by
  rw [bins_cluster_closeTouch_eq_removeBox, removeSites_closed, cluster_closed]

-- Closing a finite bond set is measurable.
example (I : Finset (Sym2 (Site 2))) :
    Measurable (fun ω : ConfigSpace (Sym2 (Site 2)) ↦ bpt2_closeI I ω) :=
  bins_measurable_closeI I

-- The exterior event depends only on bonds outside the closed set.
example (I : Finset (Sym2 (Site 2))) (u₁ u₂ u₃ : Site 2) :
    _root_.StatMech.DependsOn (bins_ExtEvent I u₁ u₂ u₃) ((↑I : Set (Sym2 (Site 2)))ᶜ) :=
  bins_ExtEvent_dependsOn I u₁ u₂ u₃

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ShellInsertionTolerance
