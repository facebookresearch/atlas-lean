/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TopNullUniqueness

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TopNullUniqueness`

* instance: for the point mass `δ₀` at the all-closed configuration, `N = ∞` is null, so
  `bc120_kne_top_of_top_null` rules out `k = ∞` for its almost-sure count `k = 0`;
* `bc120_uniqueness_of_top_null` and `bc120_bk_uniqueness_of_residues` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TopNullUniqueness

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls
open _root_.StatMech.ConfigSpace MeasureTheory
open scoped NNReal

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

-- Under `δ₀`, `N = ∞` is null and `N = 0` almost surely; so the almost-sure count is finite.
example : (0 : ℕ∞) ≠ ⊤ :=
  bc120_kne_top_of_top_null (δ₀ (d := 1)) (by rw [δ₀_N]; simp) 0 (by rw [δ₀_N]; simp)

-- With ergodicity and finite-energy merging, `N = ∞` null gives uniqueness.
example (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ) (hfe : HasFiniteEnergyMerge μ)
    (htop : μ {ω | numInfiniteClusters d ω = ⊤} = 0) :
    μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  ⟨(bc120_uniqueness_of_top_null μ herg hfe htop).2.1,
    (bc120_uniqueness_of_top_null μ herg hfe htop).2.2⟩

-- The residue route gives uniqueness for Bernoulli percolation.
example (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (L : ℕ)
    (hGlobal : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R)
    (hcoarseRoute : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 :=
  (bc120_bk_uniqueness_of_residues hd p hp1 hp0 L hGlobal hcoarseRoute).2.1

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TopNullUniqueness
