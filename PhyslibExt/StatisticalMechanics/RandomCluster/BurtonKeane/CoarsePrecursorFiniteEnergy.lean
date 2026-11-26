/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Order.Filter.Defs
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.HarmBoxCoarseReach
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalStarForest
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BernoulliErgodicFiniteEnergy

/-!
# Coarse precursors under Bernoulli percolation

For Bernoulli percolation, a coarse precursor of positive probability gives a coarse trifurcation of
positive probability, and the coarse route gives the coarse step and half of the count argument.

## i. Overview

Bernoulli percolation with `p > 0` has finite energy for merges, so a coarse precursor of positive
probability gives a coarse trifurcation of positive probability, and the coarse route gives the
coarse step. With an expectation bound of vanishing density this gives `μ(N = ⊤) = 0`.

## ii. Key results

- `bc109_coarseTrifExistence_pp` : the coarse step from the coarse route.

## iii. Table of contents

- A. Bernoulli percolation

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

/-! ## A. Bernoulli percolation -/

lemma bc109_precursor_pp (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (L : ℕ)
    (a₁ a₂ a₃ b₁ b₂ b₃ : Site d)
    (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
      (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
      {ω | bc61_IsCoarseTrifurcation ω L 0} :=
  bc62_coarseTrif_pos_of_precursor_pos
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1)
    (bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0) L a₁ a₂ a₃ b₁ b₂ b₃ hpos

lemma bc109_coarseTrifExistence_pp (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (L : ℕ)
    (hcoarseRoute : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    bc61_CoarseTrifExistence (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1) L :=
  bc62_coarseTrifExistence_of_route
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1)
    (bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0) L hcoarseRoute

lemma bc109_bk_count_half_pp (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d))
      (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1)) (L : ℕ)
    (hGlobal : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R)
    (hcoarseRoute : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
      {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc107_bk_residue_after_harmbox_discharge
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1) hd hinv
    (bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0) L hGlobal hcoarseRoute

lemma bc109_status (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) :
    (∀ (L : ℕ) (a₁ a₂ a₃ b₁ b₂ b₃ : Site d),
      0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃) →
      0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | bc61_IsCoarseTrifurcation ω L 0}) ∧
    (∀ (L : ℕ),
      (0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} →
        ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
          0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
            (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) →
      bc61_CoarseTrifExistence (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1) L) ∧
    (∀ (_hinv : IsTranslationInvariant (G := Multiplicative (Site d))
        (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1)) (L : ℕ),
      (∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R) →
      (0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} →
        ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
          0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
            (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) →
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = ⊤} = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro L a₁ a₂ a₃ b₁ b₂ b₃ hpos
    exact bc109_precursor_pp p hp1 hp0 L a₁ a₂ a₃ b₁ b₂ b₃ hpos
  · intro L hcoarseRoute
    exact bc109_coarseTrifExistence_pp p hp1 hp0 L hcoarseRoute
  · intro hinv L hGlobal hcoarseRoute
    exact bc109_bk_count_half_pp hd p hp1 hp0 hinv L hGlobal hcoarseRoute

end StatMech.Walls
