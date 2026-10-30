/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TopNullExpectation
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneErgodic
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneMerge

/-!
# The coarse merge dichotomy

If coarse trifurcations have probability zero, almost surely there are none and the forest data
hold; this excludes infinitely many infinite clusters given the coarse step.

## i. Overview

For an ergodic measure, `N` is a.s. constant. If coarse trifurcations at the origin have probability
zero, by translation invariance a.s. there are none, so the forest data hold a.s. With the coarse
step this excludes `N = ⊤`, and `N ≤ 1` a.s. gives `μ(N = ⊤) = 0`. The upper-lines configuration has
`N = ⊤` and a coarse trifurcation, so it is excluded when `μ(N = ⊤) = 0`; a coarse trifurcation does
not force two infinite clusters.

## ii. Key results

- `bc78_infinitely_many_excluded` : infinitely many infinite clusters are excluded.
- `bc78_upperLines_isInfinitelyMany` : the upper-lines configuration has `N = ⊤`.

## iii. Table of contents

- A. Probability zero and forests
- B. Excluding infinitely many clusters
- C. The upper-lines configuration

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Probability zero and forests -/

/-- Same statement as `numInfiniteClusters_ae_const`; kept because GenuineTrifAlmostSure uses it. -/
lemma bc78_numInfinite_ae_const (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (herg : IsErgodic (G := Multiplicative (Site d)) μ) :
    ∃ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1 :=
  numInfiniteClusters_ae_const μ herg

lemma bc78_ae_no_coarseTrif_of_prob_zero (μ : Measure (ConfigSpace (Sym2 (Site d)))) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (h0 : μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) :
    ∀ᵐ ω ∂μ, ∀ y : Site d, ¬ bc61_IsCoarseTrifurcation ω L y := by
  rw [MeasureTheory.ae_iff]
  have hunion : {ω | ¬ ∀ y : Site d, ¬ bc61_IsCoarseTrifurcation ω L y}
      ⊆ ⋃ y : Site d, {ω | bc61_IsCoarseTrifurcation ω L y} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, not_forall, not_not] at hω
    obtain ⟨y, hy⟩ := hω
    exact Set.mem_iUnion.mpr ⟨y, hy⟩
  refine measure_mono_null hunion ?_
  refine measure_iUnion_null ?_
  intro y
  rw [bc62_coarseTrifProb_const μ hinv L y, h0]

lemma bc78_ae_forest_of_ae_no_coarseTrif (μ : Measure (ConfigSpace (Sym2 (Site d)))) (L : ℕ)
    (hno : ∀ᵐ ω ∂μ, ∀ y : Site d, ¬ bc61_IsCoarseTrifurcation ω L y) :
    ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R := by
  intro R
  filter_upwards [hno] with ω hω
  apply bc73_sublatticeForest_of_noTrif
  rw [Finset.eq_empty_iff_forall_notMem]
  intro y hy
  rw [bc61_mem_coarseTrifFinset] at hy
  exact hω y hy.2

lemma bc78_ae_forest_of_dichotomy (μ : Measure (ConfigSpace (Sym2 (Site d)))) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (h0 : μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) :
    ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R :=
  bc78_ae_forest_of_ae_no_coarseTrif μ L (bc78_ae_no_coarseTrif_of_prob_zero μ L hinv h0)

/-! ## B. Excluding infinitely many clusters -/

lemma bc78_infinitely_many_excluded (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hforest_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R)
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc77_top_null_of_ae_forest μ hd L hinv hforest_ae hexist

lemma bc78_bk_closed (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (h0 : μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0)
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc78_infinitely_many_excluded μ hd L hinv (bc78_ae_forest_of_dichotomy μ L hinv h0) hexist

lemma bc78_top_null_of_le_one (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ]
    (hle1 : μ {ω | numInfiniteClusters d ω ≤ 1} = 1) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
  have hmeas : MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω ≤ 1} := by
    have h : {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω ≤ 1}
        = numInfiniteClusters d ⁻¹' {k : ℕ∞ | k ≤ 1} := rfl
    rw [h]; exact measurable_numInfiniteClusters (MeasurableSet.of_discrete)
  have hcompl : μ {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω ≤ 1}ᶜ = 0 :=
    (MeasureTheory.prob_compl_eq_zero_iff hmeas).mpr hle1
  refine measure_mono_null ?_ hcompl
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, hω, not_le]
  decide

/-! ## C. The upper-lines configuration -/

lemma bc78_upperLines_isInfinitelyMany :
    numInfiniteClusters 2 bc60_upperLines = ⊤ :=
  bc60_numInfiniteClusters_top

lemma bc78_upperLines_excluded_null
    (μ : Measure (ConfigSpace (Sym2 (Site 2))))
    (htop : μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) :
    μ {ω : ConfigSpace (Sym2 (Site 2)) | ω = bc60_upperLines} = 0 := by
  refine measure_mono_null ?_ htop
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [hω]; exact bc60_numInfiniteClusters_top

lemma bc78_upperLines_coarseTrif {L : ℕ} (hL : 3 ≤ L) :
    bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) ∧
      numInfiniteClusters 2 bc60_upperLines = ⊤ :=
  ⟨bc61_wholeBox_severs_upperLines hL, bc60_numInfiniteClusters_top⟩

lemma bc78_coarseTrif_not_forces_two_note :
    bc61_IsCoarseTrifurcation bc60_upperLines 3 (0 : Site 2) ∧
      numInfiniteClusters 2 bc60_upperLines = ⊤ :=
  bc78_upperLines_coarseTrif (le_refl 3)

lemma bc78_circularity_verdict (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
    ((μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) → bc61_CoarseTrifExistence μ L →
      μ {ω | numInfiniteClusters d ω = ⊤} = 0) ∧
    ((μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) →
      ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) := by
  refine ⟨fun h0 hexist => bc78_bk_closed μ hd L hinv h0 hexist, ?_⟩
  intro h0 R
  exact bc78_ae_forest_of_dichotomy μ L hinv h0 R

lemma bc78_status :
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ),
      IsTranslationInvariant (G := Multiplicative (Site 2)) μ →
      μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 →
      bc61_CoarseTrifExistence μ L →
      μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ],
      IsErgodic (G := Multiplicative (Site 2)) μ →
      μ (atLeastTwoInfinite 2) = 0 →
      μ {ω | numInfiniteClusters 2 ω ≤ 1} = 1) ∧
    (numInfiniteClusters 2 bc60_upperLines = ⊤) := by
  refine ⟨?_, ?_, ?_⟩
  · intro μ _ L hinv h0 hexist
    exact bc78_bk_closed μ (by norm_num) L hinv h0 hexist
  · intro μ _ herg hmerge
    exact StatMech.Percolation.infiniteCluster_unique_ae μ herg hmerge
  · exact bc60_numInfiniteClusters_top

end StatMech.Walls
