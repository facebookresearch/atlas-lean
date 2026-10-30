/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OriginBoxRewiring
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonicalTrifCount

/-!
# Canonical trifurcations at the origin in every box configuration

If every configuration with three distinct infinite clusters meeting `B_n` has a canonical
trifurcation at the origin, the origin rewiring route applies with the empty rewiring.

## i. Overview

`bc12_BoxOriginTrifurcation d n` asks that the origin be a canonical trifurcation in every
configuration of `threeMeetBox d n`. Its arms give box origin reach with `W = ∅`, hence the rewiring
condition and a canonical trifurcation at the origin with positive probability. An isolated origin
is never a trifurcation, so the condition fails as soon as such a configuration lies in
`threeMeetBox d n`.

## ii. Key results

- `bc12_canonicalTrif_discharges_boxReach` : a canonical trifurcation gives box origin reach
- `bc12_burtonKeane_uniqueness_of_trifurcation` : the uniqueness statement under the box condition
- `bc12_isolated_origin_not_trifurcation` : an isolated origin is not a trifurcation

## iii. Table of contents

- A. Results

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open Set SimpleGraph
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation
open MeasureTheory

namespace StatMech

namespace Walls

variable {d : ℕ}

/-! ## A. Results -/

lemma bc12_cluster_ne_of_not_connected {σ : ConfigSpace (Sym2 (Site d))} {a b : Site d}
    (h : ¬ Connected d σ a b) : cluster d σ a ≠ cluster d σ b := by
  intro heq
  exact h (mem_cluster.mp (heq ▸ self_mem_cluster σ b))

lemma bc12_openAdj_forceOpen {ω : ConfigSpace (Sym2 (Site d))} (W : Finset (Sym2 (Site d)))
    {a b : Site d} (h : (openSubgraph d ω).Adj a b) :
    (openSubgraph d (forceOpenFinset W ω)).Adj a b := by
  rw [openSubgraph_adj] at h ⊢
  refine ⟨h.1, ?_⟩
  have hle := forceOpenFinset_le W ω s(a, b)
  rw [h.2] at hle
  exact le_antisymm (by simp) hle

lemma bc12_canonicalTrif_discharges_boxReach (ω : ConfigSpace (Sym2 (Site d)))
    (htri : IsCanonicalTrifurcation d ω 0) :
    ∃ W : Finset (Sym2 (Site d)),
      (∀ e ∈ W, (0 : Site d) ∉ e) ∧
      ∃ y₁ y₂ y₃ : Site d,
        y₁ ≠ 0 ∧ y₂ ≠ 0 ∧ y₃ ≠ 0 ∧
        Connected d (forceOpenFinset W ω) 0 y₁ ∧
        Connected d (forceOpenFinset W ω) 0 y₂ ∧
        Connected d (forceOpenFinset W ω) 0 y₃ ∧
        (cluster d (removeSite 0 (forceOpenFinset W ω)) y₁).Infinite ∧
        (cluster d (removeSite 0 (forceOpenFinset W ω)) y₂).Infinite ∧
        (cluster d (removeSite 0 (forceOpenFinset W ω)) y₃).Infinite ∧
        cluster d (removeSite 0 (forceOpenFinset W ω)) y₁ ≠
          cluster d (removeSite 0 (forceOpenFinset W ω)) y₂ ∧
        cluster d (removeSite 0 (forceOpenFinset W ω)) y₁ ≠
          cluster d (removeSite 0 (forceOpenFinset W ω)) y₃ ∧
        cluster d (removeSite 0 (forceOpenFinset W ω)) y₂ ≠
          cluster d (removeSite 0 (forceOpenFinset W ω)) y₃ := by
  obtain ⟨a₁, a₂, a₃, hne, hadj, hinf, hsep⟩ := htri
  exact bc9_boxOriginReach_of_reach ω
    ((openSubgraph d ω).ne_of_adj hadj.1).symm
    ((openSubgraph d ω).ne_of_adj hadj.2.1).symm
    ((openSubgraph d ω).ne_of_adj hadj.2.2).symm
    hadj.1.reachable hadj.2.1.reachable hadj.2.2.reachable
    hinf.1 hinf.2.1 hinf.2.2
    (bc12_cluster_ne_of_not_connected hsep.1)
    (bc12_cluster_ne_of_not_connected hsep.2.1)
    (bc12_cluster_ne_of_not_connected hsep.2.2)

/-- Every configuration with three distinct infinite clusters meeting `B_n` has a canonical
trifurcation at the origin. -/
def bc12_BoxOriginTrifurcation (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n, IsCanonicalTrifurcation d ω 0

lemma bc12_boxOriginReach_of_trifurcation (n : ℕ) (h : bc12_BoxOriginTrifurcation d n) :
    bc9_BoxOriginReach d n := by
  intro ω hω
  exact bc12_canonicalTrif_discharges_boxReach ω (h ω hω)

lemma bc12_originRewiring_of_trifurcation (n : ℕ) (h : bc12_BoxOriginTrifurcation d n) :
    bc8_OriginRewiring d n :=
  bc9_originRewiring_of_boxOriginReach n (bc12_boxOriginReach_of_trifurcation n h)

lemma bc12_canonicalTrif_of_trifurcation (n : ℕ) (h : bc12_BoxOriginTrifurcation d n)
    (ω : ConfigSpace (Sym2 (Site d))) (hω : ω ∈ threeMeetBox d n) :
    ∃ W : Finset (Sym2 (Site d)), (∀ e ∈ W, (0 : Site d) ∉ e) ∧
      IsCanonicalTrifurcation d (forceOpenFinset W ω) 0 :=
  bc9_canonicalTrif_of_boxOriginReach n (bc12_boxOriginReach_of_trifurcation n h) ω hω

lemma bc12_burtonKeane_uniqueness_of_trifurcation
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (hr : ∀ n : ℕ, bc12_BoxOriginTrifurcation d n) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc9_burtonKeane_uniqueness_of_boxOriginReach μ herg hfe bdry hbound hvol hdens
    (fun n => bc12_boxOriginReach_of_trifurcation n (hr n))

lemma bc12_origin_openIncidence_of_trifurcation (ω : ConfigSpace (Sym2 (Site d)))
    (htri : IsCanonicalTrifurcation d ω 0) (W : Finset (Sym2 (Site d)))
    (_hW0 : ∀ e ∈ W, (0 : Site d) ∉ e) :
    ∃ a₁ a₂ a₃ : Site d,
      (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
      (a₁ ≠ 0 ∧ a₂ ≠ 0 ∧ a₃ ≠ 0) ∧
      ((openSubgraph d (forceOpenFinset W ω)).Adj 0 a₁ ∧
        (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₂ ∧
        (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₃) ∧
      ((cluster d (removeSite 0 ω) a₁).Infinite ∧ (cluster d (removeSite 0 ω) a₂).Infinite ∧
        (cluster d (removeSite 0 ω) a₃).Infinite) ∧
      (cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂ ∧
        cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃ ∧
        cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃) := by
  obtain ⟨a₁, a₂, a₃, hne, hadj, hinf, hsep⟩ := htri
  refine ⟨a₁, a₂, a₃, hne,
    ⟨((openSubgraph d ω).ne_of_adj hadj.1).symm,
      ((openSubgraph d ω).ne_of_adj hadj.2.1).symm,
      ((openSubgraph d ω).ne_of_adj hadj.2.2).symm⟩,
    ⟨bc12_openAdj_forceOpen W hadj.1, bc12_openAdj_forceOpen W hadj.2.1,
      bc12_openAdj_forceOpen W hadj.2.2⟩,
    hinf,
    ⟨bc12_cluster_ne_of_not_connected hsep.1,
      bc12_cluster_ne_of_not_connected hsep.2.1,
      bc12_cluster_ne_of_not_connected hsep.2.2⟩⟩

lemma bc12_isolated_origin_not_trifurcation (ω : ConfigSpace (Sym2 (Site d)))
    (hiso : ∀ v : Site d, ¬ (openSubgraph d ω).Adj 0 v) :
    ¬ IsCanonicalTrifurcation d ω 0 := by
  rintro ⟨a₁, _a₂, _a₃, _, hadj, _, _⟩
  exact hiso a₁ hadj.1

lemma bc12_boxOriginTrifurcation_perOmega_of_canonical (ω : ConfigSpace (Sym2 (Site d)))
    (htri : IsCanonicalTrifurcation d ω 0) :
    IsCanonicalTrifurcation d ω 0 ∧
    ∃ W : Finset (Sym2 (Site d)),
      (∀ e ∈ W, (0 : Site d) ∉ e) ∧
      ∃ y₁ y₂ y₃ : Site d,
        y₁ ≠ 0 ∧ y₂ ≠ 0 ∧ y₃ ≠ 0 ∧
        Connected d (forceOpenFinset W ω) 0 y₁ ∧
        Connected d (forceOpenFinset W ω) 0 y₂ ∧
        Connected d (forceOpenFinset W ω) 0 y₃ ∧
        (cluster d (removeSite 0 (forceOpenFinset W ω)) y₁).Infinite ∧
        (cluster d (removeSite 0 (forceOpenFinset W ω)) y₂).Infinite ∧
        (cluster d (removeSite 0 (forceOpenFinset W ω)) y₃).Infinite ∧
        cluster d (removeSite 0 (forceOpenFinset W ω)) y₁ ≠
          cluster d (removeSite 0 (forceOpenFinset W ω)) y₂ ∧
        cluster d (removeSite 0 (forceOpenFinset W ω)) y₁ ≠
          cluster d (removeSite 0 (forceOpenFinset W ω)) y₃ ∧
        cluster d (removeSite 0 (forceOpenFinset W ω)) y₂ ≠
          cluster d (removeSite 0 (forceOpenFinset W ω)) y₃ :=
  ⟨htri, bc12_canonicalTrif_discharges_boxReach ω htri⟩

section AxiomAudit

/-- info: 'StatMech.Walls.bc12_canonicalTrif_discharges_boxReach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bc12_canonicalTrif_discharges_boxReach

/-- info: 'StatMech.Walls.bc12_boxOriginReach_of_trifurcation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bc12_boxOriginReach_of_trifurcation

/-- info: 'StatMech.Walls.bc12_originRewiring_of_trifurcation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bc12_originRewiring_of_trifurcation

/-- info: 'StatMech.Walls.bc12_burtonKeane_uniqueness_of_trifurcation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms bc12_burtonKeane_uniqueness_of_trifurcation

/-- info: 'StatMech.Walls.bc12_origin_openIncidence_of_trifurcation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bc12_origin_openIncidence_of_trifurcation

/-- info: 'StatMech.Walls.bc12_isolated_origin_not_trifurcation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bc12_isolated_origin_not_trifurcation

end AxiomAudit

end Walls

end StatMech
