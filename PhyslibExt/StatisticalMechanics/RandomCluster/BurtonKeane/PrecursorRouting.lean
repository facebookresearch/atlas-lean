/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.FineTrifRoute

/-!
# Positive routing to trifurcation precursors

If positive probability of three distinct infinite clusters in `B_n` always yields a
positive-probability precursor after opening finitely many edges, Bernoulli percolation has at most
one infinite cluster.

## i. Overview

`brt2_PosRouting p hp1 n` says that if `threeMeetBox d n` has positive probability then some finite
edge set and neighbours `a_i` give a neighbour trifurcation precursor with positive probability
after opening the edges. A routing cover implies it, and it feeds the fine trifurcation route.

## ii. Key results

- `brt2_route_of_posRouting` : positive routing gives the trifurcation route
- `brt2_posRouting_of_routingCover` : a routing cover gives positive routing
- `brt2_bk_atLeastTwo_of_posRouting` : at most one infinite cluster from positive routing

## iii. Table of contents

- A. Definitions
- B. Results

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

/-! ## A. Definitions -/

/-- Positive routing at scale `n`: positive probability of three distinct infinite clusters meeting
`B_n` yields a finite edge set and three neighbours of the origin whose precursor, after opening
the edges, has positive probability. -/
def brt2_PosRouting (p : ℝ≥0) (hp1 : p ≤ 1) (n : ℕ) : Prop :=
  0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (threeMeetBox d n) →
    ∃ (G : Finset (Sym2 (Site d))) (a₁ a₂ a₃ : Site d),
      0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        ((fun ω => forceOpenFinset G ω) ⁻¹' NeighborTrifPrecursor d a₁ a₂ a₃)

/-! ## B. Results -/

lemma brt2_precursor_pos_of_forceOpen_pos
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) (G : Finset (Sym2 (Site d))) (a₁ a₂ a₃ : Site d)
    (hpos : 0 < μ ((fun ω => forceOpenFinset G ω) ⁻¹' NeighborTrifPrecursor d a₁ a₂ a₃)) :
    0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃) := by
  by_contra h
  rw [not_lt, nonpos_iff_eq_zero] at h
  have hac : (μ.map (fun ω => forceOpenFinset G ω)) ≪ μ := hfe G
  have hpush : (μ.map (fun ω => forceOpenFinset G ω)) (NeighborTrifPrecursor d a₁ a₂ a₃)
      = μ ((fun ω => forceOpenFinset G ω) ⁻¹' NeighborTrifPrecursor d a₁ a₂ a₃) :=
    Measure.map_apply (measurable_forceOpenFinset G)
      (hrHD_measurableSet_neighborTrifPrecursor a₁ a₂ a₃)
  have hnull : μ ((fun ω => forceOpenFinset G ω) ⁻¹' NeighborTrifPrecursor d a₁ a₂ a₃) = 0 := by
    rw [← hpush]; exact hac h
  rw [hnull] at hpos
  exact absurd rfl (ne_of_gt hpos)

lemma brt2_route_of_posRouting (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hpr : ∀ n : ℕ, brt2_PosRouting (d := d) p hp1 n) :
    ∀ n : ℕ,
      0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (threeMeetBox d n) →
        ∃ a₁ a₂ a₃ : Site d,
          0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
            (NeighborTrifPrecursor d a₁ a₂ a₃) := by
  intro n htop
  set μ := bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 with hμ
  have hfe : HasFiniteEnergyMerge μ := bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0
  obtain ⟨G, a₁, a₂, a₃, hpos⟩ := hpr n htop
  exact ⟨a₁, a₂, a₃, brt2_precursor_pos_of_forceOpen_pos μ hfe G a₁ a₂ a₃ hpos⟩

lemma brt2_posRouting_of_routingCover (p : ℝ≥0) (hp1 : p ≤ 1) {n : ℕ}
    (hrt : hrHD_DisjointRouting d n) : brt2_PosRouting (d := d) p hp1 n := by
  intro htop
  set μ := bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 with hμ
  by_contra hcon
  push Not at hcon
  have hpre0 : ∀ q : hrHD_RouteIdx d, μ (hrHD_routePre q) = 0 := by
    intro q
    have := hcon q.1 q.2.1 q.2.2.1 q.2.2.2
    exact le_antisymm this bot_le
  have hsum : (∑' q : hrHD_RouteIdx d, μ (hrHD_routePre q)) = 0 := by
    simp only [hpre0, tsum_zero]
  have hunion0 : μ (⋃ q : hrHD_RouteIdx d, hrHD_routePre q) = 0 :=
    le_antisymm (le_trans (measure_iUnion_le (μ := μ) (fun q => hrHD_routePre q))
      (le_of_eq hsum)) bot_le
  have hle : μ (threeMeetBox d n) ≤ μ (⋃ q : hrHD_RouteIdx d, hrHD_routePre q) :=
    measure_mono (hrHD_threeMeetBox_subset_iUnion_routePre hrt)
  rw [hunion0] at hle
  exact absurd (le_antisymm hle bot_le) (ne_of_gt htop)

lemma brt2_bk_of_posRouting (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hpr : ∀ n : ℕ, brt2_PosRouting (d := d) p hp1 n) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bfx_bk_of_route hd p hp1 hp0 (brt2_route_of_posRouting p hp1 hp0 hpr)

lemma brt2_bk_atLeastTwo_of_posRouting (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hpr : ∀ n : ℕ, brt2_PosRouting (d := d) p hp1 n) :
    bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 :=
  (brt2_bk_of_posRouting hd p hp1 hp0 hpr).2.1

end StatMech.Walls
