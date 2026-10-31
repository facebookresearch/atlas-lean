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
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoundaryPartitionCount

/-!
# The coarse graph of `L`-boxes

Contract each `L`-box of `ℤ^d` to a vertex; boundary classes of the coarse graph are laminar for a
single centre, and a small example shows they need not be for two centres.

## i. Overview

`bgn_idx L x` is the index of the `L`-box containing `x` and `bgn_Gn ω L` the graph on box indices
joined by an open edge. `bgn_boundaryClass ω L R u a` is the set of boundary box indices reachable
from `a` after deleting `u`. For a fixed `u` two classes are equal or disjoint, but laminarity
across different centres can fail: the eight-vertex graph `bgn_W` is a witness. The classical forest
data of the coarse graph are equivalent to the global contracted forest and give the coarse counting
bound.

The trifurcation notion here is the coarse one on `L`-boxes (`bc61_IsCoarseTrifurcation`,
`bc67_IsGnTrifurcation`), whose arms are infinite after the whole `L`-box is removed. Results that
assume a certificate for every configuration are conditional: no such certificate is constructed for
all configurations.

## ii. Key results

- `bgn_sameTrif_classes_laminar` : classes for the same centre are equal or disjoint
- `bgn_crossing_witness` : `bgn_W` has crossing classes for two centres
- `StatMech.Walls.bfa_classical_iff_bc69` (in `ClassicalForestData`) : classical forest data are the
  global contracted forest
- `StatMech.Walls.bfa_bk_of_classicalForest` (in `ClassicalForestData`) : uniqueness for Bernoulli
  percolation from classical forest data for every
  configuration
- `bgn_status` : the statements together

## iii. Table of contents

- A. Definitions
- B. Results
- C. Summary

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

/-- The index of the `L`-box (side `2L + 1`) containing `x`. -/
def bgn_idx (L : ℕ) (x : Site d) : Site d := fun i => (x i + L) / (2 * L + 1)

/-- The coarse graph: distinct box indices are adjacent when an open edge joins their boxes. -/
def bgn_Gn (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) : SimpleGraph (Site d) where
  Adj j k := j ≠ k ∧ ∃ a b : Site d, bgn_idx L a = j ∧ bgn_idx L b = k ∧ (openSubgraph d ω).Adj a b
  symm := by
    refine ⟨?_⟩
    rintro j k ⟨hjk, a, b, ha, hb, hab⟩
    exact ⟨hjk.symm, b, a, hb, ha, hab.symm⟩

/-! ## B. Results -/

@[simp] lemma bgn_Gn_adj (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (j k : Site d) :
    (bgn_Gn ω L).Adj j k ↔
      j ≠ k ∧ ∃ a b : Site d, bgn_idx L a = j ∧ bgn_idx L b = k ∧ (openSubgraph d ω).Adj a b :=
  Iff.rfl

private lemma bgn_ediv_zero {L : ℕ} {a : ℤ} (h0 : 0 ≤ a) (hlt : a < 2 * (L : ℤ) + 1) :
    a / (2 * (L : ℤ) + 1) = 0 :=
  Int.ediv_eq_zero_of_lt h0 hlt

lemma bgn_idx_adversarySite (L : ℕ) (hL : 1 ≤ L) :
    bgn_idx L (bc57_pt ((L : ℤ) + 1) 1) = bc57_pt 1 0 := by
  funext i
  fin_cases i
  · change (((bc57_pt ((L : ℤ) + 1) 1) 0) + L) / (2 * (L : ℤ) + 1) = (bc57_pt 1 0) 0
    rw [bc57_pt_fst, bc57_pt_fst]
    have : ((L : ℤ) + 1) + L = 2 * (L : ℤ) + 1 := by ring
    rw [this, Int.ediv_self (by positivity)]
  · change (((bc57_pt ((L : ℤ) + 1) 1) 1) + L) / (2 * (L : ℤ) + 1) = (bc57_pt 1 0) 1
    rw [bc57_pt_snd, bc57_pt_snd]
    exact bgn_ediv_zero (by positivity) (by omega)

lemma bgn_idx_trifCentre (L : ℕ) (hL : 1 ≤ L) :
    bgn_idx L (bc57_pt (2 * (L : ℤ) + 1) 0) = bc57_pt 1 0 := by
  funext i
  fin_cases i
  · change (((bc57_pt (2 * (L : ℤ) + 1) 0) 0) + L) / (2 * (L : ℤ) + 1) = (bc57_pt 1 0) 0
    rw [bc57_pt_fst, bc57_pt_fst]
    have hb : (2 * (L : ℤ) + 1) ≠ 0 := by positivity
    have hrw : (2 * (L : ℤ) + 1) + L = (L : ℤ) + 1 * (2 * (L : ℤ) + 1) := by ring
    rw [hrw, Int.add_mul_ediv_right _ _ hb, bgn_ediv_zero (by positivity) (by omega)]
    norm_num
  · change (((bc57_pt (2 * (L : ℤ) + 1) 0) 1) + L) / (2 * (L : ℤ) + 1) = (bc57_pt 1 0) 1
    rw [bc57_pt_snd, bc57_pt_snd]
    exact bgn_ediv_zero (by positivity) (by omega)

lemma bgn_idx_origin (L : ℕ) (hL : 1 ≤ L) :
    bgn_idx L (0 : Site 2) = bc57_pt 0 0 := by
  funext i
  fin_cases i
  · change (((0 : Site 2) 0) + L) / (2 * (L : ℤ) + 1) = (bc57_pt 0 0) 0
    rw [bc57_pt_fst]
    simpa using bgn_ediv_zero (by positivity) (by omega)
  · change (((0 : Site 2) 1) + L) / (2 * (L : ℤ) + 1) = (bc57_pt 0 0) 1
    rw [bc57_pt_snd]
    simpa using bgn_ediv_zero (by positivity) (by omega)

lemma bgn_ground_common (L : ℕ) (hL : 1 ≤ L) :
    bgn_idx L (bc57_pt ((L : ℤ) + 1) 1) = bgn_idx L (bc57_pt (2 * (L : ℤ) + 1) 0) ∧
    bgn_idx L (bc57_pt ((L : ℤ) + 1) 1) ≠ bgn_idx L (0 : Site 2) := by
  refine ⟨?_, ?_⟩
  · rw [bgn_idx_adversarySite L hL, bgn_idx_trifCentre L hL]
  · rw [bgn_idx_adversarySite L hL, bgn_idx_origin L hL]
    intro h
    have := congrFun h 0
    rw [bc57_pt_fst, bc57_pt_fst] at this
    exact one_ne_zero this

/-- Boundary box indices reachable from `a` in the coarse graph after deleting `u`. -/
def bgn_boundaryClass (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (u a : Site d) : Set (Site d) :=
  {c | c ∈ (bgn_idx L) '' (vertexBoundary d R) ∧ (bkg_deleteVertex (bgn_Gn ω L) u).Reachable a c}

lemma bgn_sameTrif_classes_laminar (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (u a b : Site d) :
    bgn_boundaryClass ω L R u a = bgn_boundaryClass ω L R u b ∨
      Disjoint (bgn_boundaryClass ω L R u a) (bgn_boundaryClass ω L R u b) := by
  by_cases h : (bkg_deleteVertex (bgn_Gn ω L) u).Reachable a b
  · left
    ext c
    simp only [bgn_boundaryClass, Set.mem_ofPred_eq]
    exact ⟨fun ⟨hc, hac⟩ => ⟨hc, h.symm.trans hac⟩, fun ⟨hc, hbc⟩ => ⟨hc, h.trans hbc⟩⟩
  · right
    rw [Set.disjoint_left]
    rintro c ⟨_, hac⟩ ⟨_, hbc⟩
    exact h (hac.trans hbc.symm)

/-- Boundary classes are laminar: any two are nested or disjoint. -/
def bgn_ClassesLaminar (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) : Prop :=
  ∀ (u u' a b : Site d),
    bgn_boundaryClass ω L R u a ⊆ bgn_boundaryClass ω L R u' b ∨
    bgn_boundaryClass ω L R u' b ⊆ bgn_boundaryClass ω L R u a ∨
    Disjoint (bgn_boundaryClass ω L R u a) (bgn_boundaryClass ω L R u' b)

lemma bgn_reach_isolated {V : Type*} {H : SimpleGraph V} {u : V}
    (hiso : ∀ z, ¬ H.Adj u z) {a : V} (h : H.Reachable a u) : a = u := by
  obtain ⟨w⟩ := h.symm
  cases w with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (hiso _)

/-- Edges of the eight-vertex example graph with two hubs `0` and `1`. -/
def bgn_Wedges : Finset (Sym2 (Fin 8)) :=
  {s(0, 1), s(0, 2), s(0, 3), s(0, 6), s(0, 7), s(1, 4), s(1, 5), s(1, 6), s(1, 7)}

/-- The eight-vertex example graph whose boundary classes cross. -/
def bgn_W : SimpleGraph (Fin 8) := SimpleGraph.fromEdgeSet (↑bgn_Wedges)

/-- Adjacency in the example graph is decidable. -/
instance : DecidableRel bgn_W.Adj := by
  unfold bgn_W; infer_instance

/-- Adjacency after deleting a vertex is decidable. -/
instance bgn_deleteVertex_decidable {V : Type*} [DecidableEq V] (Amb : SimpleGraph V)
    [DecidableRel Amb.Adj] (t : V) : DecidableRel (bkg_deleteVertex Amb t).Adj :=
  fun a b => decidable_of_iff _ (bkg_deleteVertex_adj Amb t a b).symm

lemma bgn_crossing_witness :
    (bgn_W.Adj 0 2 ∧ bgn_W.Adj 0 3 ∧ bgn_W.Adj 0 6 ∧
      ¬ (bkg_deleteVertex bgn_W 0).Reachable 2 3 ∧
      ¬ (bkg_deleteVertex bgn_W 0).Reachable 2 6 ∧
      ¬ (bkg_deleteVertex bgn_W 0).Reachable 3 6) ∧
    (bgn_W.Adj 1 4 ∧ bgn_W.Adj 1 5 ∧ bgn_W.Adj 1 6 ∧
      ¬ (bkg_deleteVertex bgn_W 1).Reachable 4 5 ∧
      ¬ (bkg_deleteVertex bgn_W 1).Reachable 4 6 ∧
      ¬ (bkg_deleteVertex bgn_W 1).Reachable 5 6) ∧
    ((bkg_deleteVertex bgn_W 0).Reachable 1 6 ∧ (bkg_deleteVertex bgn_W 1).Reachable 0 6) ∧
    ((bkg_deleteVertex bgn_W 0).Reachable 1 4 ∧ ¬ (bkg_deleteVertex bgn_W 1).Reachable 0 4) ∧
    ((bkg_deleteVertex bgn_W 1).Reachable 0 2 ∧ ¬ (bkg_deleteVertex bgn_W 0).Reachable 1 2) := by
  have iso2 : ∀ z, ¬ (bkg_deleteVertex bgn_W 0).Adj 2 z := by decide
  have iso3 : ∀ z, ¬ (bkg_deleteVertex bgn_W 0).Adj 3 z := by decide
  have iso4 : ∀ z, ¬ (bkg_deleteVertex bgn_W 1).Adj 4 z := by decide
  have iso5 : ∀ z, ¬ (bkg_deleteVertex bgn_W 1).Adj 5 z := by decide
  refine ⟨⟨by decide, by decide, by decide, ?_, ?_, ?_⟩,
          ⟨by decide, by decide, by decide, ?_, ?_, ?_⟩,
          ⟨(by decide : (bkg_deleteVertex bgn_W 0).Adj 1 6).reachable,
           (by decide : (bkg_deleteVertex bgn_W 1).Adj 0 6).reachable⟩,
          ⟨(by decide : (bkg_deleteVertex bgn_W 0).Adj 1 4).reachable, ?_⟩,
          ⟨(by decide : (bkg_deleteVertex bgn_W 1).Adj 0 2).reachable, ?_⟩⟩
  · exact fun h => absurd (bgn_reach_isolated iso2 h.symm) (by decide)
  · exact fun h => absurd (bgn_reach_isolated iso2 h.symm) (by decide)
  · exact fun h => absurd (bgn_reach_isolated iso3 h.symm) (by decide)
  · exact fun h => absurd (bgn_reach_isolated iso4 h.symm) (by decide)
  · exact fun h => absurd (bgn_reach_isolated iso4 h.symm) (by decide)
  · exact fun h => absurd (bgn_reach_isolated iso5 h.symm) (by decide)
  · exact fun h => absurd (bgn_reach_isolated iso4 h) (by decide)
  · exact fun h => absurd (bgn_reach_isolated iso2 h) (by decide)

/-! ## C. Summary -/

lemma bgn_status :
    (∀ (L : ℕ), 1 ≤ L →
      bgn_idx L (bc57_pt ((L : ℤ) + 1) 1) = bgn_idx L (bc57_pt (2 * (L : ℤ) + 1) 0) ∧
      bgn_idx L (bc57_pt ((L : ℤ) + 1) 1) ≠ bgn_idx L (0 : Site 2)) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (u a b : Site d),
      bgn_boundaryClass ω L R u a = bgn_boundaryClass ω L R u b ∨
        Disjoint (bgn_boundaryClass ω L R u a) (bgn_boundaryClass ω L R u b)) ∧
    ((bkg_deleteVertex bgn_W 0).Reachable 1 6 ∧ (bkg_deleteVertex bgn_W 1).Reachable 0 6 ∧
      (bkg_deleteVertex bgn_W 0).Reachable 1 4 ∧ ¬ (bkg_deleteVertex bgn_W 1).Reachable 0 4 ∧
      (bkg_deleteVertex bgn_W 1).Reachable 0 2 ∧ ¬ (bkg_deleteVertex bgn_W 0).Reachable 1 2) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bkg_ClassicalForestData ω L R ↔ bc69_Gn_globalForest ω L R) ∧
    (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p →
      (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bkg_ClassicalForestData ω L R) →
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) := by
  refine ⟨fun L hL => bgn_ground_common L hL, fun ω L R u a b => bgn_sameTrif_classes_laminar ω L R u a b,
    ?_, fun ω L R => bfa_classical_iff_bc69 ω L R,
    fun p hp1 hp0 hdata => bfa_bk_of_classicalForest p hp1 hp0 hdata⟩
  obtain ⟨_, _, ⟨h6a, h6b⟩, ⟨h4, h4'⟩, ⟨h2, h2'⟩⟩ := bgn_crossing_witness
  exact ⟨h6a, h6b, h4, h4', h2, h2'⟩

end StatMech.Walls
