/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BoxSurfaceVolume
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters
public import MathlibExt.Probability.Percolation.InfiniteClusterCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneUniqueness
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationCount

/-!
# Disjoint arm-end sets

Each trifurcation has a nonempty set of boundary arm ends; if these sets are pairwise disjoint, the
pigeonhole principle gives the trifurcation count.

## i. Overview

A family of nonempty, pairwise disjoint subsets of a finite set `T` has at most `|T|` members. Each
trifurcation of the box of radius `n ≥ 1` has a nonempty arm-end set `bk2_armEndFinset ω n x`,
because each infinite branch reaches the boundary, and its three branches meet the boundary in
distinct sites. Under disjointness of arm-end sets (`bk2_DisjointArmEnds`) this gives distinct arm
ends and the count bound. Disjointness fails whenever two trifurcations of the box lie in one
cluster.

The configuration-wide form of this condition, for every configuration and every box of radius
`n ≥ 1`, is unsatisfiable when `d ≥ 1`: it implies `Tcount d ω n ≤ boxSV_boundaryCard d n` for every
configuration, which `tfc_not_forall_Tcount_le_boundary` refutes (`bk2_not_forall_disjointArmEnds`).
The Burton–Keane theorem that assumed it was removed as vacuous.

## ii. Key results

- `bk2_card_le_of_pairwiseDisjoint` : the pigeonhole bound for disjoint nonempty sets.
- `bk2_Tcount_le_boundary_of_disjointArmEnds` : the count bound from disjoint arm ends.

## iii. Table of contents

- A. Pigeonhole
- B. Arm-end sets
- C. Three boundary arms
- D. Unsatisfiability of the configuration-wide conditions

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}

/-! ## A. Pigeonhole -/

set_option linter.unusedDecidableInType false in
lemma bk2_card_le_of_pairwiseDisjoint {α β : Type*} [DecidableEq β]
    (S : Finset α) (T : Finset β) (A : α → Finset β)
    (hne : ∀ x ∈ S, (A x).Nonempty)
    (hsub : ∀ x ∈ S, A x ⊆ T)
    (hdisj : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Disjoint (A x) (A y)) :
    S.card ≤ T.card := by
  classical
  rcases S.eq_empty_or_nonempty with hS | hS
  · simp [hS]
  · obtain ⟨x₀, hx₀⟩ := hS
    obtain ⟨b₀, _⟩ := hne x₀ hx₀
    let φ : α → β := fun x => if h : (A x).Nonempty then h.choose else b₀
    refine Finset.card_le_card_of_injOn φ ?_ ?_
    · intro x hx
      simp only [Finset.mem_coe] at hx ⊢
      have h := hne x hx
      simp only [φ, dite_eq_left h]
      exact hsub x hx h.choose_spec
    · intro x hx y hy hxy
      simp only [Finset.mem_coe] at hx hy
      by_cases hne' : x = y
      · exact hne'
      · exfalso
        have hAx := hne x hx
        have hAy := hne y hy
        simp only [φ, dite_eq_left hAx, dite_eq_left hAy] at hxy
        have hmem : hAx.choose ∈ A x ∩ A y :=
          Finset.mem_inter.mpr ⟨hAx.choose_spec, hxy ▸ hAy.choose_spec⟩
        rw [Finset.disjoint_iff_inter_eq_empty.mp (hdisj x hx y hy hne')] at hmem
        exact absurd hmem (Finset.notMem_empty _)

/-! ## B. Arm-end sets -/

open Classical in
/-- The boundary sites of the box of radius `n` connected to `x`. -/
noncomputable def bk2_armEndFinset (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (x : Site d) :
    Finset (Site d) :=
  (tfc_boundaryFinset d n).filter (fun z => Connected d ω x z)

lemma bk2_mem_armEndFinset {ω : ConfigSpace (Sym2 (Site d))} {n : ℕ} {x z : Site d} :
    z ∈ bk2_armEndFinset ω n x ↔ z ∈ vertexBoundary d n ∧ Connected d ω x z := by
  classical
  rw [bk2_armEndFinset, Finset.mem_filter, tfc_mem_boundaryFinset]

lemma bk2_armEndFinset_subset (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (x : Site d) :
    bk2_armEndFinset ω n x ⊆ tfc_boundaryFinset d n := by
  classical
  exact Finset.filter_subset _ _

lemma bk2_armEndFinset_nonempty (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (x : Site d) (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x) :
    (bk2_armEndFinset ω n x).Nonempty := by
  obtain ⟨z, hzb, hzc⟩ := tfc_trif_reaches_boundary ω n hn x hxbox htri
  exact ⟨z, bk2_mem_armEndFinset.mpr ⟨hzb, hzc⟩⟩

/-- Distinct trifurcations of the box have disjoint arm-end sets. -/
def bk2_DisjointArmEnds (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
    x ≠ y → Disjoint (bk2_armEndFinset ω n x) (bk2_armEndFinset ω n y)

lemma bk2_distinctArmEnds_of_disjoint (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (hdisj : bk2_DisjointArmEnds ω n) :
    tfc_DistinctArmEnds ω n := by
  classical
  set sel : Site d → Site d := fun x =>
    if h : x ∈ box d n ∧ IsTrifurcation d ω x then
      (bk2_armEndFinset_nonempty ω n hn x h.1 h.2).choose else x with hsel
  refine ⟨sel, ?_, ?_⟩
  · intro x hxbox htri
    have hspec :=
      (bk2_armEndFinset_nonempty ω n hn x hxbox htri).choose_spec
    rw [bk2_mem_armEndFinset] at hspec
    simp only [hsel, dite_eq_left (⟨hxbox, htri⟩ : x ∈ box d n ∧ IsTrifurcation d ω x)]
    exact hspec
  · intro x hxbox htri y hybox htriy hxy
    by_contra hne
    have hxspec :=
      (bk2_armEndFinset_nonempty ω n hn x hxbox htri).choose_spec
    have hyspec :=
      (bk2_armEndFinset_nonempty ω n hn y hybox htriy).choose_spec
    simp only [hsel, dite_eq_left (⟨hxbox, htri⟩ : x ∈ box d n ∧ IsTrifurcation d ω x),
      dite_eq_left (⟨hybox, htriy⟩ : y ∈ box d n ∧ IsTrifurcation d ω y)] at hxy
    have hmem : (bk2_armEndFinset_nonempty ω n hn x hxbox htri).choose
        ∈ bk2_armEndFinset ω n x ∩ bk2_armEndFinset ω n y :=
      Finset.mem_inter.mpr ⟨hxspec, hxy ▸ hyspec⟩
    rw [Finset.disjoint_iff_inter_eq_empty.mp
        (hdisj x hxbox htri y hybox htriy hne)] at hmem
    exact absurd hmem (Finset.notMem_empty _)

lemma bk2_Tcount_le_boundary_of_disjointArmEnds (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (hdisj : bk2_DisjointArmEnds ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  tfc_Tcount_le_boundary_of_distinctArmEnds ω n
    (bk2_distinctArmEnds_of_disjoint ω n hn hdisj)

lemma bk2_disjointArmEnds_of_subsingleton (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hsub : ∀ x y, x ∈ box d n → IsTrifurcation d ω x → y ∈ box d n →
      IsTrifurcation d ω y → x = y) :
    bk2_DisjointArmEnds ω n := by
  intro x hxbox htri y hybox htriy hxy
  exact absurd (hsub x y hxbox htri hybox htriy) hxy

/-! ## C. Three boundary arms -/

lemma bk2_branch_reaches_boundary_rem (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (x a : Site d) (habox : a ∈ box d n) (hinf : (cluster d (removeSite x ω) a).Infinite) :
    ∃ z ∈ vertexBoundary d n, Connected d (removeSite x ω) a z := by
  classical
  obtain ⟨y, hybox, hyconn⟩ := (cluster_infinite_iff (removeSite x ω) a).mp hinf n
  obtain ⟨w⟩ := hyconn
  obtain ⟨b, c, hbc, hb, hc, hr⟩ :=
    tfc_walk_crossing (openSubgraph d (removeSite x ω)) (fun v => v ∈ box d n) w habox hybox
  have hblat : (hypercubicLattice d).Adj b c := (openSubgraph_le (removeSite x ω)) hbc
  exact ⟨b, tfc_boundary_cross_vertex n hn b c hb hc hblat, hr⟩

lemma bk2_armEnds_disconnected (ω : ConfigSpace (Sym2 (Site d))) {x a₁ a₂ z₁ z₂ : Site d}
    (hz1 : Connected d (removeSite x ω) a₁ z₁)
    (hz2 : Connected d (removeSite x ω) a₂ z₂)
    (hdis : ¬ Connected d (removeSite x ω) a₁ a₂) :
    ¬ Connected d (removeSite x ω) z₁ z₂ :=
  fun hc => hdis (hz1.trans (hc.trans hz2.symm))

lemma bk2_armEnds_distinct_of_disconnected (ω : ConfigSpace (Sym2 (Site d)))
    {x z₁ z₂ : Site d} (hdis : ¬ Connected d (removeSite x ω) z₁ z₂) : z₁ ≠ z₂ := by
  rintro rfl; exact hdis connected_rfl

lemma bk2_trif_three_disjoint_boundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    {x a₁ a₂ a₃ : Site d}
    (ha1box : a₁ ∈ box d n) (ha2box : a₂ ∈ box d n) (ha3box : a₃ ∈ box d n)
    (hi1 : (cluster d (removeSite x ω) a₁).Infinite)
    (hi2 : (cluster d (removeSite x ω) a₂).Infinite)
    (hi3 : (cluster d (removeSite x ω) a₃).Infinite)
    (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
    (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
    (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) :
    ∃ z₁ z₂ z₃ : Site d,
      (z₁ ∈ vertexBoundary d n ∧ z₂ ∈ vertexBoundary d n ∧ z₃ ∈ vertexBoundary d n) ∧
      (Connected d (removeSite x ω) a₁ z₁ ∧ Connected d (removeSite x ω) a₂ z₂ ∧
        Connected d (removeSite x ω) a₃ z₃) ∧
      (¬ Connected d (removeSite x ω) z₁ z₂ ∧ ¬ Connected d (removeSite x ω) z₁ z₃ ∧
        ¬ Connected d (removeSite x ω) z₂ z₃) ∧
      (z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃) := by
  obtain ⟨z₁, hz1b, hz1c⟩ := bk2_branch_reaches_boundary_rem ω n hn x a₁ ha1box hi1
  obtain ⟨z₂, hz2b, hz2c⟩ := bk2_branch_reaches_boundary_rem ω n hn x a₂ ha2box hi2
  obtain ⟨z₃, hz3b, hz3c⟩ := bk2_branch_reaches_boundary_rem ω n hn x a₃ ha3box hi3
  have hzd12 := bk2_armEnds_disconnected ω hz1c hz2c hd12
  have hzd13 := bk2_armEnds_disconnected ω hz1c hz3c hd13
  have hzd23 := bk2_armEnds_disconnected ω hz2c hz3c hd23
  exact ⟨z₁, z₂, z₃, ⟨hz1b, hz2b, hz3b⟩, ⟨hz1c, hz2c, hz3c⟩, ⟨hzd12, hzd13, hzd23⟩,
    ⟨bk2_armEnds_distinct_of_disconnected ω hzd12,
      bk2_armEnds_distinct_of_disconnected ω hzd13,
      bk2_armEnds_distinct_of_disconnected ω hzd23⟩⟩

/-! ## D. Unsatisfiability of the configuration-wide conditions -/

/-- `bk2_DisjointArmEnds` for every configuration and every box of radius `n ≥ 1` is impossible when
`d ≥ 1`: this implies the configuration-wide bound `Tcount ≤ |∂Λₙ|`, which
`tfc_not_forall_Tcount_le_boundary` refutes. -/
lemma bk2_not_forall_disjointArmEnds (hd : 1 ≤ d) :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      bk2_DisjointArmEnds ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary hd fun ω n hn =>
    bk2_Tcount_le_boundary_of_disjointArmEnds ω n hn (h ω n hn)

end Percolation

end StatMech
