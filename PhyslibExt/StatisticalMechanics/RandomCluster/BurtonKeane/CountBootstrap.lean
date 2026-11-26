/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.FiberLeafBoundary
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineTrifUpperLines
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SingleBoxCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TopNullFiniteVolume

/-!
# The coarse count bootstrap

The expected coarse count with a forest bound gives probability zero, and with the coarse step this
excludes infinitely many infinite clusters; this ordering is not circular.

## i. Overview

For a translation-invariant measure the expected coarse count is
`|Λ_R| · P(coarse trifurcation at 0)`. A per-configuration forest bound of vanishing density then
gives probability zero, and with the coarse step `μ(N = ⊤) = 0`; for an ergodic measure with finite
energy this gives uniqueness. The bound is used before `N` is known to be finite, so the argument is
not circular. Finite `N` alone does not give the bound: a coarse trifurcation needs three infinite
arms, and in the upper-lines configuration two disjoint boxes are both coarse trifurcations while
`N = ⊤`.

## ii. Key results

- `bc85_prob_zero_of_count_forest` : probability zero from a forest bound.
- `bc85_dc_step1_uniqueness` : uniqueness from the forest bound and the coarse step.

## iii. Table of contents

- A. Expectation and probability zero
- B. Finite `N`
- C. Ordering of the argument

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

/-! ## A. Expectation and probability zero -/

lemma bc85_prob_zero_of_count_forest (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hforest_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) :
    μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 :=
  bc77_coarseTrif_prob_eq_zero_ae μ L
    (fun R => (2 * L + 1) ^ d * boxSV_boundaryCard d R)
    (fun R => bc62_coarse_expectation μ hinv L R)
    (bc77_ae_bound_of_ae_forest μ L hforest_ae)
    (fun R => bkc_boxFinsetBK_card_pos d R)
    (bc73_const_boundary_vol_tendsto d hd L)

lemma bc85_exclude_infinite_N (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (L : ℕ)
    (h0 : μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0)
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
  by_contra htop
  have hpos : 0 < μ {ω | numInfiniteClusters d ω = ⊤} := pos_iff_ne_zero.mpr htop
  have := hexist hpos
  rw [h0] at this
  exact lt_irrefl 0 this

lemma bc85_dc_step1_uniqueness (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hforest_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R)
    (hexist : bc61_CoarseTrifExistence μ L)
    (hmergeGeom : ∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters d ω = k} = 1 →
      ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k)) :
    μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  have htop : μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
    bc77_top_null_of_ae_forest μ hd L hinv hforest_ae hexist
  have hkne_top : ∀ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1 → k ≠ ⊤ := by
    intro k hk hktop
    rw [hktop] at hk; rw [hk] at htop; exact one_ne_zero htop
  have hmerge : μ (atLeastTwoInfinite d) = 0 :=
    merge_event_null μ herg hfe hkne_top hmergeGeom
  exact infiniteCluster_unique_ae μ herg hmerge

/-! ## B. Finite `N` -/

lemma bc85_finiteN_not_enough_note {L : ℕ} (hL : 3 ≤ L) :
    bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) ∧
    Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc76_yBuf L)) ∧
    ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable
      ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩
      ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ :=
  bc76_buffer_insufficient hL

/-! ## C. Ordering of the argument -/

lemma bc85_bootstrap_noncircular_order (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
    ((μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) →
      ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) ∧
    ((μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) → bc61_CoarseTrifExistence μ L →
      μ {ω | numInfiniteClusters d ω = ⊤} = 0) := by
  refine ⟨fun h0 => bc78_ae_forest_of_dichotomy μ L hinv h0, ?_⟩
  intro h0 hexist
  exact bc85_exclude_infinite_N μ L h0 hexist

lemma bc85_circularity_verdict (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
    ((∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) → bc61_CoarseTrifExistence μ L →
      μ {ω | numInfiniteClusters d ω = ⊤} = 0) ∧
    ((μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) →
      ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) ∧
    (μ {ω | numInfiniteClusters d ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters d ω = ⊤} = 0) := by
  refine ⟨fun hforest_ae hexist => bc77_top_null_of_ae_forest μ hd L hinv hforest_ae hexist, ?_, ?_⟩
  · intro h0; exact bc78_ae_forest_of_dichotomy μ L hinv h0
  · exact bc79_finite_N_iff_top_null μ

lemma bc85_status :
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ),
      IsTranslationInvariant (G := Multiplicative (Site 2)) μ →
      (∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) →
      bc61_CoarseTrifExistence μ L →
      μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ),
      IsErgodic (G := Multiplicative (Site 2)) μ → HasFiniteEnergyMerge μ →
      IsTranslationInvariant (G := Multiplicative (Site 2)) μ →
      (∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) →
      bc61_CoarseTrifExistence μ L →
      (∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters 2 ω = k} = 1 →
        ∃ F : Finset (Sym2 (Site 2)), 0 < μ (MergeWitness 2 F k)) →
      μ {ω | numInfiniteClusters 2 ω ≤ 1} = 1) ∧
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ],
      (μ {ω | numInfiniteClusters 2 ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters 2 ω = ⊤} = 0)) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y : Site 2), numInfiniteClusters 2 ω ≤ 1 →
      bc61_IsCoarseTrifurcation ω L y →
      ∃ a₁ a₂ a₃ : Site 2, Connected 2 ω a₁ a₂ ∧ Connected 2 ω a₁ a₃ ∧ Connected 2 ω a₂ a₃) ∧
    (numInfiniteClusters 2 bc60_upperLines = ⊤) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro μ _ L hinv hforest_ae hexist
    exact bc77_top_null_of_ae_forest μ (by norm_num) L hinv hforest_ae hexist
  · intro μ _ L herg hfe hinv hforest_ae hexist hmergeGeom
    exact bc85_dc_step1_uniqueness μ (by norm_num) L herg hfe hinv hforest_ae hexist hmergeGeom
  · intro μ _; exact bc79_finite_N_iff_top_null μ
  · intro ω L y hN h
    obtain ⟨a₁, a₂, a₃, hc₁₂, hc₁₃, hc₂₃, _⟩ := bc81_coarseTrif_arms_connected_of_le_one ω L hN h
    exact ⟨a₁, a₂, a₃, hc₁₂, hc₁₃, hc₂₃⟩
  · exact bc60_numInfiniteClusters_top

end StatMech.Walls
