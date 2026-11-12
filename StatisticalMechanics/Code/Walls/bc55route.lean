/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































































import Mathlib
import Code.Walls.bc54coarse
import Code.Walls.bc49finiteenergy
import Code.Percolation.BoxMergeFreeMenger

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

















theorem bc55_hroute_of_routingCover (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hrt : ∀ n : ℕ, hrHD_DisjointRouting d n) :
    ∀ n : ℕ,
      0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (threeMeetBox d n) →
        ∃ a₁ a₂ a₃ : Site d,
          0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
            (NeighborTrifPrecursor d a₁ a₂ a₃) :=
  hrHD_route_of_routing (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1)
    (bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0) hrt



















theorem bc55_hroute_of_boxMengerAttachment (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hattach : ∀ n : ℕ, bmm_BoxMengerAttachment d n) :
    ∀ n : ℕ,
      0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (threeMeetBox d n) →
        ∃ a₁ a₂ a₃ : Site d,
          0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
            (NeighborTrifPrecursor d a₁ a₂ a₃) :=
  bc55_hroute_of_routingCover p hp1 hp0
    (fun n => bmm_disjointRouting_of_attachment (hattach n))


















theorem bc55_burton_keane_bernoulli_of_boxMenger (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p) (hattach : ∀ n : ℕ, bmm_BoxMengerAttachment d n) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc54_burton_keane_bernoulli hd p hp1 hp0
    (bc55_hroute_of_boxMengerAttachment p hp1 hp0 hattach)





theorem bc55_burton_keane_bernoulli_of_routingCover (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p) (hrt : ∀ n : ℕ, hrHD_DisjointRouting d n) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc54_burton_keane_bernoulli hd p hp1 hp0 (bc55_hroute_of_routingCover p hp1 hp0 hrt)

























theorem bc55_boxMenger_forces_originNeighbour_in_cluster (n : ℕ)
    (hattach : bmm_BoxMengerAttachment d n)
    (ω : ConfigSpace (Sym2 (Site d))) (hω : ω ∈ threeMeetBox d n)
    (x₁ x₂ x₃ : Site d) (hb1 : x₁ ∈ box d n) (hb2 : x₂ ∈ box d n) (hb3 : x₃ ∈ box d n)
    (hi1 : (cluster d ω x₁).Infinite) (hi2 : (cluster d ω x₂).Infinite)
    (hi3 : (cluster d ω x₃).Infinite)
    (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂) (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
    (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃) :
    (∃ a : Site d, (hypercubicLattice d).Adj 0 a ∧ a ∈ cluster d ω x₁) ∧
    (∃ a : Site d, (hypercubicLattice d).Adj 0 a ∧ a ∈ cluster d ω x₂) ∧
    (∃ a : Site d, (hypercubicLattice d).Adj 0 a ∧ a ∈ cluster d ω x₃) := by
  obtain ⟨a₁, a₂, a₃, W, ⟨hadj1, hadj2, hadj3⟩, _, ⟨ha1, ha2, ha3⟩, _, _, _⟩ :=
    hattach ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  exact ⟨⟨a₁, hadj1, ha1⟩, ⟨a₂, hadj2, ha2⟩, ⟨a₃, hadj3, ha3⟩⟩











theorem bc55_originNeighbour_avoiding_cluster (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hno : ∀ a : Site d, (hypercubicLattice d).Adj 0 a → a ∉ cluster d ω x) :
    ¬ ∃ a : Site d, (hypercubicLattice d).Adj 0 a ∧ a ∈ cluster d ω x := by
  rintro ⟨a, hadj, ha⟩
  exact hno a hadj ha








theorem bc55_naive_collapse_false_of_notNeighbour (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hxne : ∀ a : Site d, (hypercubicLattice d).Adj 0 a → a ≠ x) :
    ¬ ((hypercubicLattice d).Adj 0 x ∧ x ∈ cluster d ω x) := by
  rintro ⟨hadj, _⟩
  exact hxne x hadj rfl
















theorem bc55_boxMenger_zeroObstacle_witness (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x₁ ∧ (hypercubicLattice d).Adj 0 x₂ ∧
      (hypercubicLattice d).Adj 0 x₃)
    (hri : (cluster d (removeSite 0 ω) x₁).Infinite ∧
      (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) :
    ∃ (a₁ a₂ a₃ : Site d) (W : Finset (Sym2 (Site d))),
      ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
        (hypercubicLattice d).Adj 0 a₃) ∧
      (∀ e ∈ W, (0 : Site d) ∉ e) ∧
      (a₁ ∈ cluster d ω x₁ ∧ a₂ ∈ cluster d ω x₂ ∧ a₃ ∈ cluster d ω x₃) ∧
      ((∀ u v, u ∈ cluster d ω x₁ → s(u, v) ∈ W → v ∈ cluster d ω x₁) ∧
        (∀ u v, u ∈ cluster d ω x₂ → s(u, v) ∈ W → v ∈ cluster d ω x₂) ∧
        (∀ u v, u ∈ cluster d ω x₃ → s(u, v) ∈ W → v ∈ cluster d ω x₃)) ∧
      (Connected d (removeSite 0 (forceOpenFinset W ω)) a₁ x₁ ∧
        Connected d (removeSite 0 (forceOpenFinset W ω)) a₂ x₂ ∧
        Connected d (removeSite 0 (forceOpenFinset W ω)) a₃ x₃) ∧
      ((cluster d (removeSite 0 ω) x₁).Infinite ∧
        (cluster d (removeSite 0 ω) x₂).Infinite ∧
        (cluster d (removeSite 0 ω) x₃).Infinite) :=
  bmm_attachment_of_neighbour_witnesses ω x₁ x₂ x₃ hadj hri






















theorem bc55_status (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) :
    ((∀ n : ℕ, bmm_BoxMengerAttachment d n) →
      ∀ n : ℕ,
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (threeMeetBox d n) →
          ∃ a₁ a₂ a₃ : Site d,
            0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
              (NeighborTrifPrecursor d a₁ a₂ a₃)) ∧
    ((∀ n : ℕ, bmm_BoxMengerAttachment d n) →
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0) :=
  ⟨fun hattach => bc55_hroute_of_boxMengerAttachment p hp1 hp0 hattach,
   fun hattach => (bc55_burton_keane_bernoulli_of_boxMenger hd p hp1 hp0 hattach).2.1⟩

end StatMech.Walls
