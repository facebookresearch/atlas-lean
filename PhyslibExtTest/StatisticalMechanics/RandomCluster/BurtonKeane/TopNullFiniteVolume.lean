/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TopNullFiniteVolume

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TopNullFiniteVolume`

* `bc79_enat_012top` and `bc79_le_one_of_012top_ne_top` at `k = 1`;
* instance: for the point mass `δ₀` at the all-closed configuration, `N = ∞` is null, so
  `bc79_finite_N_iff_top_null` gives `N < ∞` almost surely;
* `bc79_top_subset_atLeastTwo` and `bc79_top_null_of_merge_null` (conditional form);
* `bc79_directCount_refuted_on_upperLines` at `L = 3`: the origin of `bc60_upperLines` is a
  contracted-lattice trifurcation.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TopNullFiniteVolume

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls
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

/-- The all-closed configuration has no infinite cluster. -/
theorem num_closed : numInfiniteClusters d (fun _ => false) = 0 := by
  rw [numInfiniteClusters, Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
  rintro C ⟨hC, x, rfl⟩
  rw [cluster_closed] at hC
  exact hC (Set.finite_singleton x)

/-- The point mass at the all-closed configuration. -/
noncomputable def δ₀ : Measure (ConfigSpace (Sym2 (Site d))) := Measure.dirac (fun _ => false)

instance : IsProbabilityMeasure (δ₀ (d := d)) := by
  rw [δ₀]
  infer_instance

/-- Under `δ₀` the number of infinite clusters is `k` with probability `1` if `k = 0`, else `0`. -/
theorem δ₀_N (k : ℕ∞) : δ₀ {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = k}
    = if k = 0 then 1 else 0 := by
  have hs : MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = k} :=
    measurable_numInfiniteClusters (measurableSet_singleton k)
  rw [δ₀, Measure.dirac_apply' _ hs]
  by_cases hk : k = 0 <;> simp [Set.indicator, num_closed, hk, eq_comm]

-- A count that jumps from `2` straight to `∞` is `0`, `1` or `∞`; if finite, it is at most `1`.
example : (1 : ℕ∞) ≤ 1 :=
  bc79_le_one_of_012top_ne_top (bc79_enat_012top fun h => absurd h (by decide)) ENat.one_ne_top

-- Under `δ₀`, `N = ∞` is null, hence `N < ∞` almost surely.
example : δ₀ {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω < ⊤} = 1 :=
  (bc79_finite_N_iff_top_null δ₀).mpr (by rw [δ₀_N]; simp)

-- `N = ∞` is part of the event of at least two infinite clusters.
example (μ : Measure (ConfigSpace (Sym2 (Site d)))) (h : μ (atLeastTwoInfinite d) = 0) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 ∧
      {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = ⊤} ⊆ atLeastTwoInfinite d :=
  ⟨bc79_top_null_of_merge_null μ h, bc79_top_subset_atLeastTwo⟩

-- The direct count is refuted by the upper-lines configuration.
example : bc67_IsGnTrifurcation bc60_upperLines 3 (0 : Site 2) :=
  (bc79_directCount_refuted_on_upperLines le_rfl).1

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TopNullFiniteVolume
