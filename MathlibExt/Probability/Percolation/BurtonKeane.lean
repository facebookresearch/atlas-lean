/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.InfiniteClusterCount
import MathlibExt.Probability.Percolation.BurtonKeane.EncounterConstruction

/-!
# Uniqueness of the infinite cluster in Bernoulli bond percolation

The Burton–Keane theorem for Bernoulli bond percolation on `ℤ^d`: for every `p ∈ [0, 1]` there is
almost surely at most one infinite open cluster.

The ported library proves that the number of infinite clusters `N` is almost surely constant
under any translation-ergodic measure (`StatMech.Percolation.numInfiniteClusters_ae_const`).
Opening a finite box rules out a finite constant greater than one. An infinite constant would
give positive probability to an encounter point, contradicting the boundary bound on their number.

## Main statements

* `burton_keane_bernoulli`: `N ≤ 1` almost surely under `bernoulliProductMeasure p`.

## References

* R. M. Burton, M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
* G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

namespace MathlibExt.Probability.Percolation.BurtonKeaneWanted

open MeasureTheory StatMech StatMech.Percolation StatMech.Lattice StatMech.ConfigSpace
open scoped NNReal

private theorem count_le_one_iff (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) :
    numInfiniteClusters d ω ≤ 1 ↔
      ∀ x y, (cluster d ω x).Infinite → (cluster d ω y).Infinite → Connected d ω x y := by
  rw [numInfiniteClusters, Set.encard_le_one_iff_subsingleton]
  constructor
  · intro h x y hx hy
    have heq := h (show cluster d ω x ∈ infiniteClusters d ω from ⟨hx, x, rfl⟩)
      (show cluster d ω y ∈ infiniteClusters d ω from ⟨hy, y, rfl⟩)
    exact (mem_cluster.mp (heq ▸ self_mem_cluster ω y : y ∈ cluster d ω x))
  · rintro h _ ⟨hx, x, rfl⟩ _ ⟨hy, y, rfl⟩
    exact cluster_eq_of_connected (h x y hx hy)

private theorem ae_count_le_one_dim_zero (p : ℝ≥0) (hp : p ≤ 1) :
    ∀ᵐ ω ∂(bernoulliProductMeasure (E := Sym2 (Site 0)) p hp), numInfiniteClusters 0 ω ≤ 1 := by
  apply Filter.Eventually.of_forall
  intro ω
  rw [count_le_one_iff]
  exact fun x _ hx => (hx (Set.toFinite _)).elim

private theorem ae_count_le_one_one (d : ℕ) (hp : (1 : ℝ≥0) ≤ 1) :
    ∀ᵐ ω ∂(bernoulliProductMeasure (E := Sym2 (Site d)) 1 hp), numInfiniteClusters d ω ≤ 1 := by
  have hb : bernoulliMeasure 1 hp = Measure.dirac true :=
    ProbabilityTheory.bernoulliMeasure_one _ _
  rw [bernoulliProductMeasure, hb, Measure.infinitePi_dirac, ae_dirac_iff]
  · rw [count_le_one_iff]
    intro x y _ _
    have hopen : openSubgraph d (fun _ => true) = hypercubicLattice d := by ext; simp
    rw [Connected, hopen]
    obtain ⟨n, hn⟩ := finite_subset_box {x, y} ((Set.finite_singleton y).insert x)
    exact (box_preconnected n ⟨x, hn (by simp)⟩ ⟨y, hn (by simp)⟩).map
      (SimpleGraph.Embedding.induce _).toHom
  · exact measurable_numInfiniteClusters (MeasurableSet.of_discrete (s := Set.Iic 1))


private theorem ae_count_le_one_zero (d : ℕ) (hp : (0 : ℝ≥0) ≤ 1) :
    ∀ᵐ ω ∂(bernoulliProductMeasure (E := Sym2 (Site d)) 0 hp), numInfiniteClusters d ω ≤ 1 := by
  have hb : bernoulliMeasure 0 hp = Measure.dirac false :=
    ProbabilityTheory.bernoulliMeasure_zero _ _
  rw [bernoulliProductMeasure, hb, Measure.infinitePi_dirac, ae_dirac_iff]
  · rw [count_le_one_iff]
    intro x _ hx
    have hg : openSubgraph d (fun _ => false) = ⊥ := by ext; simp
    have hs : cluster d (fun _ => false) x ⊆ {x} := by
      intro y hy
      rw [mem_cluster, Connected, hg, SimpleGraph.reachable_bot] at hy
      exact hy.symm
    exact (hx ((Set.finite_singleton x).subset hs)).elim
  · exact measurable_numInfiniteClusters (MeasurableSet.of_discrete (s := Set.Iic 1))

/-- **Burton–Keane theorem** for Bernoulli bond percolation. For every dimension `d` and every
`p ∈ [0, 1]`, almost surely under the Bernoulli(`p`) bond percolation measure on `ℤ^d` there is
at most one infinite open cluster.

Source: R. M. Burton, M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121
(1989), 501–505. -/
public theorem burton_keane_bernoulli :
    ∀ (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1),
      ∀ᵐ ω ∂(bernoulliProductMeasure (E := Sym2 (Lattice.Site d)) p hp),
        numInfiniteClusters d ω ≤ 1 := by
  intro d p hp
  rcases d with _ | d
  · exact ae_count_le_one_dim_zero p hp
  rcases eq_or_lt_of_le hp with rfl | hp1
  · exact ae_count_le_one_one _ hp
  rcases eq_or_lt_of_le (show 0 ≤ p from zero_le) with h | hp0
  · subst p
    exact ae_count_le_one_zero _ hp
  let μ := bernoulliProductMeasure (E := Sym2 (Site (d + 1))) p hp
  have hd : 1 ≤ d + 1 := Nat.le_add_left 1 d
  have he := bernoulli_lattice_ergodic hd p hp
  obtain ⟨k, hk⟩ := numInfiniteClusters_ae_const μ he
  have hfinite : k ≠ ⊤ := by
    rintro rfl
    have hpos : 0 < μ {ω | numInfiniteClusters (d + 1) ω = ⊤} := hk ▸ zero_lt_one
    have henc := measure_encounter_pos_of_infinite_count μ he.isTranslationInvariant
      (map_setPattern_absolutelyContinuous hp0 hp1) hpos
    exact henc.ne' (measure_encounter_eq_zero μ hd he.isTranslationInvariant)
  have hle : k ≤ 1 := enat_le_one_of_not_two fun htwo =>
    hfinite (burton_keane_merge_excludes_finite_ge_two μ (bernoulli_finiteEnergyMerge p hp hp0)
      (fun j hj _ => exists_mergeWitness_pos μ j hj) k hk htwo)
  have hae : ∀ᵐ ω ∂μ, numInfiniteClusters (d + 1) ω = k :=
    (mem_ae_iff_prob_eq_one (measurable_numInfiniteClusters (measurableSet_singleton k))).mpr hk
  filter_upwards [hae] with ω hω
  exact hω.trans_le hle

end MathlibExt.Probability.Percolation.BurtonKeaneWanted
