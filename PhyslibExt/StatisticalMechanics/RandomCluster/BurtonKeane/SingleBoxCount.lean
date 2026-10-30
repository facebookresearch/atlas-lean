/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GnCoarseInfiniteCluster

/-!
# Expected coarse trifurcation counts

By translation invariance the expected coarse count is the volume times the origin probability;
without an upper bound for every configuration this gives no contradiction.

## i. Overview

For a translation-invariant measure the expected number of coarse trifurcations in `B_R` is `|B_R| ·
μ(coarse trifurcation at 0)`. The coarse count is at most the volume and equals it when every site
is a coarse trifurcation, so single-box information gives no counting bound. The leaf-count
certificate supplies the needed bound.

The trifurcation notion here is the coarse one on `L`-boxes (`bc61_IsCoarseTrifurcation`,
`bc67_IsGnTrifurcation`), whose arms are infinite after the whole `L`-box is removed. Results that
assume a certificate for every configuration are conditional: no such certificate is constructed for
all configurations.

## ii. Key results

- `bc82_coarseTcount_eq_volume_of_all_trif` : the count can equal the volume
- `bc82_status` : the statements together

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
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Results -/

lemma bc82_coarseTcount_le_volume (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) :
    bc61_coarseTcount ω L R ≤ (boxFinsetBK d R).card := by
  classical
  rw [bc61_coarseTcount, bc61_coarseTrifFinset]
  exact Finset.card_filter_le _ _

lemma bc82_coarseTcount_eq_volume_of_all_trif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (hall : ∀ y ∈ boxFinsetBK d R, bc61_IsCoarseTrifurcation ω L y) :
    bc61_coarseTcount ω L R = (boxFinsetBK d R).card := by
  classical
  rw [bc61_coarseTcount, bc61_coarseTrifFinset, Finset.filter_true_of_mem hall]

lemma bc82_singleBox_gives_no_count_bound (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (hall : ∀ y ∈ boxFinsetBK d R, bc61_IsCoarseTrifurcation ω L y) :
    (∀ y ∈ boxFinsetBK d R, ∃ a₁ a₂ a₃ : Site d,
      ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧
      ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧
      ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) ∧
    bc61_coarseTcount ω L R = (boxFinsetBK d R).card := by
  refine ⟨?_, bc82_coarseTcount_eq_volume_of_all_trif ω L R hall⟩
  intro y hy
  obtain ⟨a₁, a₂, a₃, _, hcut⟩ := bc81_singleBox_no_gap ω L y (hall y hy)
  exact ⟨a₁, a₂, a₃, hcut⟩

lemma bc82_expected_needs_upper_bound (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (L : ℕ) (bdry : ℕ → ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc61_coarseTcount ω L R ≤ bdry R)
    (hvol : ∀ R, 0 < (boxFinsetBK d R).card)
    (hdens : Filter.Tendsto
      (fun R => (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0)) :
    μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 :=
  bc61_coarseTrif_prob_eq_zero μ L bdry
    (fun R => bc62_coarse_expectation μ hinv L R) hbound hvol hdens

lemma bc82_borelCantelli_route_fails {L : ℕ} (hL : 3 ≤ L) :
    bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) ∧
    Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc76_yBuf L)) ∧
    ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable
      ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩
      ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ :=
  bc81_route1_fails hL

lemma bc82_cardinal_verdict (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hd : 1 ≤ d) (L : ℕ)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
    (∀ R : ℕ, ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
      = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc73_SublatticeForest ω L R →
      bc61_coarseTcount ω L R ≤ (2 * L + 1) ^ d * boxSV_boundaryCard d R) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ),
      (∀ y ∈ boxFinsetBK d R, bc61_IsCoarseTrifurcation ω L y) →
      bc61_coarseTcount ω L R = (boxFinsetBK d R).card) ∧
    ((μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) → bc61_CoarseTrifExistence μ L →
      μ {ω | numInfiniteClusters d ω = ⊤} = 0) := by
  refine ⟨fun R => bc77_expected_count μ hinv L R, ?_, ?_, ?_⟩
  · intro ω R h; exact bc73_covering ω L R h
  · intro ω R hall; exact bc82_coarseTcount_eq_volume_of_all_trif ω L R hall
  · intro h0 hexist; exact bc79_bk_from_leaf μ hd L hinv h0 hexist

/-! ## B. Summary -/

lemma bc82_status :
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) (L R : ℕ),
      IsTranslationInvariant (G := Multiplicative (Site 2)) μ →
      ((boxFinsetBK 2 R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
        = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bc73_SublatticeForest ω L R →
      bc61_coarseTcount ω L R ≤ (2 * L + 1) ^ 2 * boxSV_boundaryCard 2 R) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ),
      (∀ y ∈ boxFinsetBK 2 R, bc61_IsCoarseTrifurcation ω L y) →
      (∀ y ∈ boxFinsetBK 2 R, ∃ a₁ a₂ a₃ : Site 2,
        ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧
        ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧
        ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) ∧
      bc61_coarseTcount ω L R = (boxFinsetBK 2 R).card) ∧
    (∀ {L : ℕ}, 3 ≤ L →
      ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable
        ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩
        ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩) ∧
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ),
      IsTranslationInvariant (G := Multiplicative (Site 2)) μ →
      μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 → bc61_CoarseTrifExistence μ L →
      μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro μ L R hinv; exact bc77_expected_count μ hinv L R
  · intro ω L R h; exact bc73_covering ω L R h
  · intro ω L R hall; exact bc82_singleBox_gives_no_count_bound ω L R hall
  · intro L hL; exact (bc82_borelCantelli_route_fails hL).2.2
  · intro μ _ L hinv h0 hexist; exact bc79_bk_from_leaf μ (by norm_num) L hinv h0 hexist

end StatMech.Walls
