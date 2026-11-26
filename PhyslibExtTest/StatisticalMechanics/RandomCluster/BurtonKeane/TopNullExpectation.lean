/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TopNullExpectation

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TopNullExpectation`

* `bc77_upperLines_singleton`: the singleton of `bc60_upperLines` as a set-builder;
* `bc77_ae_bound_of_ae_forest` in conditional form;
* `bc77_coarseTrif_prob_eq_zero_ae` and `bc77_top_null_of_ae_forest` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TopNullExpectation

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls
open _root_.StatMech.ConfigSpace MeasureTheory
open scoped ENNReal

variable {d : ℕ}

-- The singleton of the upper-lines configuration.
example : ({bc60_upperLines} : Set (ConfigSpace (Sym2 (Site 2)))) = {ω | ω = bc60_upperLines} :=
  bc77_upperLines_singleton

-- An almost-sure fibre bound gives an almost-sure coarse count bound.
example (μ : Measure (ConfigSpace (Sym2 (Site d)))) (L : ℕ)
    (hforest_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) (R : ℕ) :
    ∀ᵐ ω ∂μ, bc61_coarseTcount ω L R ≤ (2 * L + 1) ^ d * boxSV_boundaryCard d R :=
  bc77_ae_bound_of_ae_forest μ L hforest_ae R

-- An almost-sure `o(|B_R|)` bound forces zero coarse-trifurcation probability.
example (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (L : ℕ)
    (bdry : ℕ → ℕ)
    (hexp : ∀ R : ℕ, ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
      = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
    (hbound_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, bc61_coarseTcount ω L R ≤ bdry R)
    (hvol : ∀ R, 0 < (boxFinsetBK d R).card)
    (hdens : Filter.Tendsto (fun R => (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop
      (nhds 0)) :
    μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 :=
  bc77_coarseTrif_prob_eq_zero_ae μ L bdry hexp hbound_ae hvol hdens

-- Almost-sure fibre bounds and coarse existence exclude `N = ∞`.
example (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d)
    (L : ℕ) (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hforest_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R)
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc77_top_null_of_ae_forest μ hd L hinv hforest_ae hexist

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TopNullExpectation
