/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































import Mathlib
import Code.Walls.bfxtrifexist

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


















def brt2_PosRouting (p : ℝ≥0) (hp1 : p ≤ 1) (n : ℕ) : Prop :=
  0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (threeMeetBox d n) →
    ∃ (G : Finset (Sym2 (Site d))) (a₁ a₂ a₃ : Site d),
      0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        ((fun ω => forceOpenFinset G ω) ⁻¹' NeighborTrifPrecursor d a₁ a₂ a₃)














theorem brt2_precursor_pos_of_forceOpen_pos
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











theorem brt2_route_of_posRouting (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
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














theorem brt2_posRouting_of_routingCover (p : ℝ≥0) (hp1 : p ≤ 1) {n : ℕ}
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










theorem brt2_bk_of_posRouting (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hpr : ∀ n : ℕ, brt2_PosRouting (d := d) p hp1 n) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bfx_bk_of_route hd p hp1 hp0 (brt2_route_of_posRouting p hp1 hp0 hpr)




theorem brt2_bk_atLeastTwo_of_posRouting (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hpr : ∀ n : ℕ, brt2_PosRouting (d := d) p hp1 n) :
    bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 :=
  (brt2_bk_of_posRouting hd p hp1 hp0 hpr).2.1

end StatMech.Walls
