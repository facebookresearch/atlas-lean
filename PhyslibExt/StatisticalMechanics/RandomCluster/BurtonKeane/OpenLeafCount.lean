/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseForestProbCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TopNullUniqueness

/-!
# Open leaf edges and expected counts

The expected number of open edges in a finite edge set is at most its size; forests whose leaves are
open edges therefore exclude `N = ∞` under translation invariance.

## i. Overview

`bel_leafOpenCount F ω` counts the open edges of `F`. Its expectation is at most `|F|`. If the
coarse trifurcations of `B_R` are bounded by the open leaves of a forest whose leaf edges `F R` grow
like the boundary, translation invariance forces the coarse trifurcation probability to vanish,
which excludes `N = ∞` and gives uniqueness for Bernoulli percolation.

The trifurcation notion here is the coarse one on `L`-boxes (`bc61_IsCoarseTrifurcation`,
`bc67_IsGnTrifurcation`), whose arms are infinite after the whole `L`-box is removed. Results that
assume a certificate for every configuration are conditional: no such certificate is constructed for
all configurations.

## ii. Key results

- `bel_expLeaf_le` : the expected open count is at most `|F|`
- `bel_top_null_of_forest_open` : open-leaf forests exclude `N = ∞`
- `bel_status` : the statements together

## iii. Table of contents

- A. Results
- B. Summary

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Results -/

/-- The event that the edge `e` is open is measurable. See also
`StatMech.FK.idc_openEdgeEvent_measurable`, the same statement. -/
lemma bel_measurableSet_edgeOpen (e : Sym2 (Site d)) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | ω e = true} :=
  measurableSet_eq_fun (measurable_pi_apply e) measurable_const

/-- The number of open edges of `ω` in `F`. -/
def bel_leafOpenCount (F : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d))) : ℕ :=
  (F.filter (fun e => ω e = true)).card

lemma bel_leafOpenCount_eq_sum_indicator (ω : ConfigSpace (Sym2 (Site d)))
    (F : Finset (Sym2 (Site d))) :
    (bel_leafOpenCount F ω : ℝ≥0∞) =
      ∑ e ∈ F, ({ω' : ConfigSpace (Sym2 (Site d)) | ω' e = true}.indicator (fun _ => (1 : ℝ≥0∞))) ω := by
  classical
  rw [bel_leafOpenCount, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : ω e = true
  · rw [ite_eq_left h, Set.indicator_of_mem (show ω ∈ {ω' | ω' e = true} from h)]
  · rw [ite_eq_right h, Set.indicator_of_notMem (show ω ∉ {ω' | ω' e = true} from h)]

lemma bel_expLeaf_le (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (F : Finset (Sym2 (Site d))) :
    ∫⁻ ω, (bel_leafOpenCount F ω : ℝ≥0∞) ∂μ ≤ (F.card : ℝ≥0∞) := by
  classical
  have hmeas : ∀ e : Sym2 (Site d), Measurable
      (fun ω : ConfigSpace (Sym2 (Site d)) =>
        ({ω' | ω' e = true}.indicator (fun _ => (1 : ℝ≥0∞))) ω) :=
    fun e => Measurable.indicator measurable_const (bel_measurableSet_edgeOpen e)
  calc ∫⁻ ω, (bel_leafOpenCount F ω : ℝ≥0∞) ∂μ
      = ∫⁻ ω, ∑ e ∈ F,
          ({ω' : ConfigSpace (Sym2 (Site d)) | ω' e = true}.indicator (fun _ => (1 : ℝ≥0∞))) ω ∂μ := by
        apply lintegral_congr; intro ω; exact bel_leafOpenCount_eq_sum_indicator ω F
    _ = ∑ e ∈ F, ∫⁻ ω,
          ({ω' : ConfigSpace (Sym2 (Site d)) | ω' e = true}.indicator (fun _ => (1 : ℝ≥0∞))) ω ∂μ := by
        rw [MeasureTheory.lintegral_finsetSum]; intro e _; exact hmeas e
    _ = ∑ e ∈ F, μ {ω : ConfigSpace (Sym2 (Site d)) | ω e = true} := by
        apply Finset.sum_congr rfl; intro e _
        rw [MeasureTheory.lintegral_indicator (bel_measurableSet_edgeOpen e)]; simp
    _ ≤ ∑ _e ∈ F, (1 : ℝ≥0∞) := by
        apply Finset.sum_le_sum; intro e _; exact prob_le_one
    _ = (F.card : ℝ≥0∞) := by simp

lemma bel_top_null_of_forest_open
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) (hd : 1 ≤ d) (L : ℕ)
    (F : ℕ → Finset (Sym2 (Site d)))
    (hforest : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ),
      bpe_CoarseForestNoBnd ω L R (bel_leafOpenCount (F R) ω))
    (hdens : Filter.Tendsto
      (fun R => ((F R).card : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0))
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bpe_top_null_of_probForest μ hinv hd L (fun R => (F R).card)
    (fun ω R => bel_leafOpenCount (F R) ω) hforest
    (fun R => bel_expLeaf_le μ (F R)) hdens hexist

lemma bel_bk_uniqueness_of_forest_open (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (L : ℕ)
    (F : ℕ → Finset (Sym2 (Site d)))
    (hforest : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ),
      bpe_CoarseForestNoBnd ω L R (bel_leafOpenCount (F R) ω))
    (hdens : Filter.Tendsto
      (fun R => ((F R).card : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0))
    (hcoarseRoute : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  set μ := bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 with hμ
  have herg : IsErgodic (G := Multiplicative (Site d)) μ := bkc_bernoulli_isErgodic hd p hp1
  have hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ := herg.isTranslationInvariant
  have hfe : HasFiniteEnergyMerge μ := bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0
  have hexist : bc61_CoarseTrifExistence μ L := bc109_coarseTrifExistence_pp p hp1 hp0 L hcoarseRoute
  have htop : μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
    bel_top_null_of_forest_open μ hinv hd L F hforest hdens hexist
  exact bc120_uniqueness_of_top_null μ herg hfe htop

/-! ## B. Summary -/

lemma bel_status (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (F : ℕ → Finset (Sym2 (Site d))) :
    (∀ R : ℕ, ∫⁻ ω, (bel_leafOpenCount (F R) ω : ℝ≥0∞) ∂μ ≤ ((F R).card : ℝ≥0∞)) ∧
    (IsTranslationInvariant (G := Multiplicative (Site d)) μ → 1 ≤ d → ∀ L : ℕ,
      (∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ),
        bpe_CoarseForestNoBnd ω L R (bel_leafOpenCount (F R) ω)) →
      Filter.Tendsto (fun R => ((F R).card : ℝ) / ((boxFinsetBK d R).card : ℝ))
        Filter.atTop (nhds 0) →
      bc61_CoarseTrifExistence μ L →
      μ {ω | numInfiniteClusters d ω = ⊤} = 0) := by
  refine ⟨fun R => bel_expLeaf_le μ (F R), ?_⟩
  intro hinv hd L hforest hdens hexist
  exact bel_top_null_of_forest_open μ hinv hd L F hforest hdens hexist

end StatMech.Walls
