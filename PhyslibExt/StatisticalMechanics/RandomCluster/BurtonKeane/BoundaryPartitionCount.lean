/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.FinCases
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SeparatedBoxDegree
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalForestLeafCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClassicalVertexForest

/-!
# Boundary classes of coarse trifurcations

The arms of a coarse trifurcation split the boundary into three disjoint reachability classes;
classical forest data are the global forest and give the coarse count.

## i. Overview

`bpt_boundaryClass ω L R x a` is the set of boundary sites reachable from `a` in the contracted
lattice at `x`. A coarse trifurcation has three arms with nonempty, pairwise disjoint classes.
Classes of one trifurcation are laminar (equal or disjoint); `bpt_ClassesLaminar` asks this across
trifurcations, but the cut ground sets of two boxes differ. Classical forest data
`bkg_ClassicalForestData` are equivalent to the global forest and give the coarse count and
uniqueness on `ℤ²`.

## ii. Key results

- `bpt_trif_three_classes_disjoint` : three disjoint boundary classes.
- `StatMech.Walls.bkg_coarseTcount_of_classical` (in `ClassicalVertexForest`) : the coarse count
  from classical forest data.

## iii. Table of contents

- A. Boundary classes
- B. Laminarity
- C. The count

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

/-! ## A. Boundary classes -/

/-- The boundary sites of the box of radius `R` reachable from `a` in the contracted lattice at `x`.
-/
def bpt_boundaryClass (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (x a : Site d) : Set (Site d) :=
  {c | c ∈ vertexBoundary d R ∧ (bc67_contractedLattice ω L x).Reachable a c}

lemma bpt_mem_boundaryClass {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ} {x a c : Site d} :
    c ∈ bpt_boundaryClass ω L R x a ↔
      c ∈ vertexBoundary d R ∧ (bc67_contractedLattice ω L x).Reachable a c :=
  Iff.rfl

lemma bpt_trif_three_boundary_classes (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hR : 1 ≤ R)
    {x : Site d} (arm : Fin 3 → Site d)
    (harmbox : ∀ i, arm i ∈ box d R)
    (harmne : ∀ i, arm i ≠ x)
    (harminf : ∀ i, (cluster d (removeSites (bc61_boxAround d L x) ω) (arm i)).Infinite)
    (harmsep : ∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (arm i) (arm j)) :
    ∃ t : Fin 3 → Site d,
      (∀ i, t i ∈ vertexBoundary d R) ∧
      (∀ i, t i ≠ x) ∧
      Function.Injective (fun i => (bc67_contractedLattice ω L x).connectedComponentMk (t i)) := by
  classical
  obtain ⟨t, hbdry, hreach, hne, hsep⟩ :=
    bsd_arm_tips_of_separated ω L R hR arm harmbox harmne harminf harmsep
  refine ⟨t, hbdry, hne, ?_⟩
  intro i j hij
  by_contra hij'
  exact hsep i j hij' (SimpleGraph.ConnectedComponent.eq.mp hij)

lemma bpt_trif_three_classes_disjoint (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hR : 1 ≤ R)
    {x : Site d} (arm : Fin 3 → Site d)
    (harmbox : ∀ i, arm i ∈ box d R)
    (harmne : ∀ i, arm i ≠ x)
    (harminf : ∀ i, (cluster d (removeSites (bc61_boxAround d L x) ω) (arm i)).Infinite)
    (harmsep : ∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (arm i) (arm j)) :
    ∃ t : Fin 3 → Site d,
      (∀ i, t i ∈ bpt_boundaryClass ω L R x (t i)) ∧
      (∀ i j, i ≠ j → Disjoint (bpt_boundaryClass ω L R x (t i)) (bpt_boundaryClass ω L R x (t
          j))) := by
  classical
  obtain ⟨t, hbdry, hreach, hne, hsep⟩ :=
    bsd_arm_tips_of_separated ω L R hR arm harmbox harmne harminf harmsep
  refine ⟨t, ?_, ?_⟩
  · intro i; exact ⟨hbdry i, SimpleGraph.Reachable.refl _⟩
  · intro i j hij
    rw [Set.disjoint_left]
    rintro c ⟨_, hci⟩ ⟨_, hcj⟩
    exact hsep i j hij (hci.trans hcj.symm)

/-! ## B. Laminarity -/

lemma bpt_sameTrif_classes_laminar (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (x a b : Site d) :
    bpt_boundaryClass ω L R x a = bpt_boundaryClass ω L R x b ∨
      Disjoint (bpt_boundaryClass ω L R x a) (bpt_boundaryClass ω L R x b) := by
  by_cases h : (bc67_contractedLattice ω L x).Reachable a b
  · left
    ext c
    simp only [bpt_mem_boundaryClass]
    constructor
    · rintro ⟨hc, hac⟩; exact ⟨hc, h.symm.trans hac⟩
    · rintro ⟨hc, hbc⟩; exact ⟨hc, h.trans hbc⟩
  · right
    rw [Set.disjoint_left]
    rintro c ⟨_, hac⟩ ⟨_, hbc⟩
    exact h (hac.trans hbc.symm)

/-- Boundary classes of any two coarse trifurcations are equal or disjoint. -/
def bpt_ClassesLaminar (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) : Prop :=
  ∀ (x x' a b : Site d), bc67_IsGnTrifurcation ω L x → bc67_IsGnTrifurcation ω L x' →
    a ∈ vertexBoundary d R → b ∈ vertexBoundary d R →
    bpt_boundaryClass ω L R x a ⊆ bpt_boundaryClass ω L R x' b ∨
    bpt_boundaryClass ω L R x' b ⊆ bpt_boundaryClass ω L R x a ∨
    Disjoint (bpt_boundaryClass ω L R x a) (bpt_boundaryClass ω L R x' b)

lemma bpt_cut_ground_sets_differ (L : ℕ) (hL : 1 ≤ L) :
    (bc57_pt ((L : ℤ) + 1) 1) ∉ bc61_boxAround 2 L (0 : Site 2) ∧
    (bc57_pt ((L : ℤ) + 1) 1) ∈ bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0) := by
  constructor
  · rw [bc61_mem_boxAround_zero, mem_box]; push Not
    refine ⟨0, ?_⟩
    change ((bc57_pt ((L : ℤ) + 1) 1) 0).natAbs > L
    rw [bc57_pt_fst]; omega
  · rw [bc61_mem_boxAround, mem_box]
    intro i; fin_cases i
    · change ((bc57_pt ((L : ℤ) + 1) 1 - bc57_pt (2 * (L : ℤ) + 1) 0) 0).natAbs ≤ L
      rw [Pi.sub_apply, bc57_pt_fst, bc57_pt_fst]; omega
    · change ((bc57_pt ((L : ℤ) + 1) 1 - bc57_pt (2 * (L : ℤ) + 1) 0) 1).natAbs ≤ L
      rw [Pi.sub_apply, bc57_pt_snd, bc57_pt_snd]; omega

/-! ## C. The count -/

lemma bpt_status :
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 1 ≤ R → ∀ (x : Site d) (arm : Fin 3 → Site d),
      (∀ i, arm i ∈ box d R) → (∀ i, arm i ≠ x) →
      (∀ i, (cluster d (removeSites (bc61_boxAround d L x) ω) (arm i)).Infinite) →
      (∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (arm i) (arm j)) →
      ∃ t : Fin 3 → Site d,
        (∀ i, t i ∈ bpt_boundaryClass ω L R x (t i)) ∧
        (∀ i j, i ≠ j →
          Disjoint (bpt_boundaryClass ω L R x (t i)) (bpt_boundaryClass ω L R x (t j)))) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (x a b : Site d),
      bpt_boundaryClass ω L R x a = bpt_boundaryClass ω L R x b ∨
        Disjoint (bpt_boundaryClass ω L R x a) (bpt_boundaryClass ω L R x b)) ∧
    (∀ (L : ℕ), 1 ≤ L →
      (bc57_pt ((L : ℤ) + 1) 1) ∉ bc61_boxAround 2 L (0 : Site 2) ∧
      (bc57_pt ((L : ℤ) + 1) 1) ∈ bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      (bkg_ClassicalForestData ω L R ↔ bc69_Gn_globalForest ω L R) ∧
      (bkg_ClassicalForestData ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω L R hR x arm harmbox harmne harminf harmsep
    exact bpt_trif_three_classes_disjoint ω L R hR arm harmbox harmne harminf harmsep
  · intro ω L R x a b
    exact bpt_sameTrif_classes_laminar ω L R x a b
  · intro L hL
    exact bpt_cut_ground_sets_differ L hL
  · intro ω L R
    exact ⟨bfa_classical_iff_bc69 ω L R, bkg_coarseTcount_of_classical ω L R⟩

end StatMech.Walls
