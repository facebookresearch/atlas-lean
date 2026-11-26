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
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseBoundaryTrifCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClassicalPrecursorFiniteEnergy
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoxMergeFreeMenger

/-!
# Uniqueness from Menger attachment

Disjoint routing or Menger attachment in every box gives the route hypothesis and Burton–Keane
uniqueness for Bernoulli percolation; Menger attachment forces neighbours of the origin into the
clusters.

## i. Overview

Disjoint routing (`hrHD_DisjointRouting`) or box Menger attachment in every box gives the route
hypothesis for Bernoulli percolation with `p > 0`, and then uniqueness of the infinite cluster.
Menger attachment puts a neighbour of the origin in each of the three clusters, so it fails for a
cluster avoiding all neighbours of the origin.

The uniqueness theorems here assume the attachment or routing condition for every box; the condition
is not proved in general.

## ii. Key results

- `bc55_burton_keane_bernoulli_of_boxMenger` : uniqueness from Menger attachment in every box.
- `bc55_burton_keane_bernoulli_of_routingCover` : uniqueness from disjoint routing in every box.

## iii. Table of contents

- A. The route and uniqueness
- B. Necessary conditions

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), Section 8.2.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. The route and uniqueness -/

lemma bc55_hroute_of_routingCover (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hrt : ∀ n : ℕ, hrHD_DisjointRouting d n) :
    ∀ n : ℕ,
      0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (threeMeetBox d n) →
        ∃ a₁ a₂ a₃ : Site d,
          0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
            (NeighborTrifPrecursor d a₁ a₂ a₃) :=
  hrHD_route_of_routing (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1)
    (bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0) hrt

lemma bc55_hroute_of_boxMengerAttachment (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hattach : ∀ n : ℕ, bmm_BoxMengerAttachment d n) :
    ∀ n : ℕ,
      0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (threeMeetBox d n) →
        ∃ a₁ a₂ a₃ : Site d,
          0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
            (NeighborTrifPrecursor d a₁ a₂ a₃) :=
  bc55_hroute_of_routingCover p hp1 hp0
    (fun n => bmm_disjointRouting_of_attachment (hattach n))

lemma bc55_burton_keane_bernoulli_of_boxMenger (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
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

lemma bc55_burton_keane_bernoulli_of_routingCover (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p) (hrt : ∀ n : ℕ, hrHD_DisjointRouting d n) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc54_burton_keane_bernoulli hd p hp1 hp0 (bc55_hroute_of_routingCover p hp1 hp0 hrt)

/-! ## B. Necessary conditions -/

lemma bc55_boxMenger_forces_originNeighbour_in_cluster (n : ℕ)
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

lemma bc55_originNeighbour_avoiding_cluster (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hno : ∀ a : Site d, (hypercubicLattice d).Adj 0 a → a ∉ cluster d ω x) :
    ¬ ∃ a : Site d, (hypercubicLattice d).Adj 0 a ∧ a ∈ cluster d ω x := by
  rintro ⟨a, hadj, ha⟩
  exact hno a hadj ha

lemma bc55_naive_collapse_false_of_notNeighbour (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hxne : ∀ a : Site d, (hypercubicLattice d).Adj 0 a → a ≠ x) :
    ¬ ((hypercubicLattice d).Adj 0 x ∧ x ∈ cluster d ω x) := by
  rintro ⟨hadj, _⟩
  exact hxne x hadj rfl

lemma bc55_status (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) :
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
