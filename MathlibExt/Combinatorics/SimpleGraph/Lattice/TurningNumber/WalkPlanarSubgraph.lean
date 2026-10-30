/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanEnclosureDuality
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.JordanParity
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.DirectionWalk
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.WalkCrossing
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.WalkVertices
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.InsidePropagation

/-!
# A simple closed walk as a planar subgraph of the square lattice

A simple closed walk of length `m + 3` with directions `d` embeds the cycle graph
`cycleGraph (m + 3)` into the square lattice `ℤ²`. The cycle has nullity (cycle rank) `1`, so by
the discrete Jordan curve theorem for planar subgraphs of `ℤ²`
(`StatMech.Lattice.jed_faithfulDiscreteJordan`, which identifies the bounded faces with the
nullity) the walk has exactly one bounded face.

## Main definitions

* `StatMech.Onsager.JedBridge.posSite`: the walk vertices as sites of `ℤ²`.
* `StatMech.Onsager.JedBridge.walkSubgraph`: the walk as a `StatMech.Lattice.PlanarZ2Subgraph`.

## Main results

* `StatMech.Onsager.JedBridge.cycle_nullity_one`: the cycle graph has nullity `1`.
* `StatMech.Onsager.JedBridge.walk_one_bounded_region`: a simple closed lattice walk has exactly
  one bounded face (the lattice Jordan curve theorem for the walk).
-/

@[expose] public section

namespace StatMech.Onsager.JedBridge

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.WalkCrossing
  StatMech.Onsager.NoDoubleWind StatMech.Onsager.JordanParity StatMech.Onsager.InsideClimb
open StatMech.Lattice
open SimpleGraph

/-- The `i`-th vertex of the walk as a site of `ℤ²`. -/
def posSite {m : ℕ} (d : Fin (m + 3) → Fin 4) (i : Fin (m + 3)) : Site 2 :=
  ![(pos d i).1, (pos d i).2]

@[simp] theorem posSite_zero {m : ℕ} (d : Fin (m + 3) → Fin 4) (i : Fin (m + 3)) :
    (posSite d i) 0 = (pos d i).1 := rfl

@[simp] theorem posSite_one {m : ℕ} (d : Fin (m + 3) → Fin 4) (i : Fin (m + 3)) :
    (posSite d i) 1 = (pos d i).2 := rfl

/-- The vertices of a simple walk are distinct sites. -/
theorem posSite_injective {m : ℕ} (d : Fin (m + 3) → Fin 4)
    (hsimple : Function.Injective (pos d)) : Function.Injective (posSite d) := by
  intro i j h
  have h0 : (posSite d i) 0 = (posSite d j) 0 := by rw [h]
  have h1 : (posSite d i) 1 = (posSite d j) 1 := by rw [h]
  rw [posSite_zero, posSite_zero] at h0
  rw [posSite_one, posSite_one] at h1
  exact hsimple (Prod.ext h0 h1)

/-- Each step has `ℓ¹`-length `1`. -/
theorem stepOf_natAbs_sum (w : Fin 4) :
    (stepOf w).1.natAbs + (stepOf w).2.natAbs = 1 := by
  fin_cases w <;> rfl

/-- Consecutive vertices of the walk are adjacent in the square lattice. -/
theorem walk_isSub {m : ℕ} (d : Fin (m + 3) → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    ⦃i j : Fin (m + 3)⦄ (hadj : (cycleGraph (m + 3)).Adj i j) :
    (hypercubicLattice 2).Adj (posSite d i) (posSite d j) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  rw [cycleGraph_adj] at hadj
  rcases hadj with h | h
  · have hij : j + 1 = i := (add_comm j 1).trans (sub_eq_iff_eq_add.mp h).symm
    have hs := pos_succ d hclosed j
    rw [hij] at hs
    have e0 : (posSite d i) 0 - (posSite d j) 0 = (stepOf (d j)).1 := by
      rw [posSite_zero, posSite_zero, hs, Prod.fst_add]; ring
    have e1 : (posSite d i) 1 - (posSite d j) 1 = (stepOf (d j)).2 := by
      rw [posSite_one, posSite_one, hs, Prod.snd_add]; ring
    rw [e0, e1]; exact stepOf_natAbs_sum (d j)
  · have hji : i + 1 = j := (add_comm i 1).trans (sub_eq_iff_eq_add.mp h).symm
    have hs := pos_succ d hclosed i
    rw [hji] at hs
    have e0 : (posSite d i) 0 - (posSite d j) 0 = -(stepOf (d i)).1 := by
      rw [posSite_zero, posSite_zero, hs, Prod.fst_add]; ring
    have e1 : (posSite d i) 1 - (posSite d j) 1 = -(stepOf (d i)).2 := by
      rw [posSite_one, posSite_one, hs, Prod.snd_add]; ring
    rw [e0, e1, Int.natAbs_neg, Int.natAbs_neg]; exact stepOf_natAbs_sum (d i)

/-- A simple closed walk as a planar subgraph of `ℤ²`: the cycle graph `cycleGraph (m + 3)` embedded
  by its vertex positions. -/
noncomputable def walkSubgraph {m : ℕ} (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d)) :
    PlanarZ2Subgraph where
  V := Fin (m + 3)
  finV := inferInstance
  decV := inferInstance
  G := cycleGraph (m + 3)
  emb := ⟨posSite d, posSite_injective d hsimple⟩
  isSub := walk_isSub d hclosed

/-- A cycle graph has one connected component. A specialization of
  `SimpleGraph.Preconnected.subsingleton_connectedComponent`. -/
theorem cycleGraph_card_components_one (m : ℕ) :
    Nat.card (cycleGraph (m + 3)).ConnectedComponent = 1 :=
  Nat.card_eq_one_iff_unique.mpr
    ⟨connected_cycleGraph_add_one.preconnected.subsingleton_connectedComponent,
      ⟨(cycleGraph (m + 3)).connectedComponentMk 0⟩⟩

/-- The cycle graph on `m + 3` vertices has `m + 3` edges. -/
theorem cycleGraph_card_edges (m : ℕ) :
    (cycleGraph (m + 3)).edgeSet.ncard = m + 3 := by
  have hsum : ∑ v : Fin (m + 3), (cycleGraph (m + 3)).degree v
      = 2 * (cycleGraph (m + 3)).edgeFinset.card :=
    (cycleGraph (m + 3)).sum_degrees_eq_twice_card_edges
  have hdeg : ∀ v : Fin (m + 3), (cycleGraph (m + 3)).degree v = 2 :=
    fun v => cycleGraph_degree_three_le
  rw [Finset.sum_congr rfl (fun v _ => hdeg v), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hsum
  have hcard : (cycleGraph (m + 3)).edgeFinset.card = m + 3 := by omega
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, hcard]

/-- The cycle graph has nullity (cycle rank) `1`. -/
theorem cycle_nullity_one (m : ℕ) : nullity (cycleGraph (m + 3)) = 1 := by
  unfold nullity
  rw [cycleGraph_card_edges m, cycleGraph_card_components_one m,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

/-- The planar subgraph of a simple closed walk has nullity `1`. -/
theorem walkSubgraph_nullity_one {m : ℕ} (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d)) :
    nullity (walkSubgraph d hclosed hsimple).G = 1 := by
  change nullity (cycleGraph (m + 3)) = 1
  exact cycle_nullity_one m

/-- Lattice Jordan curve theorem for a simple closed walk: its complement in the face graph of `ℤ²`
  has exactly one bounded connected component. -/
theorem walk_one_bounded_region {m : ℕ} (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d)) :
    Nat.card {c : (whb_faceRegion (imageGraph (walkSubgraph d hclosed hsimple))).ConnectedComponent
      // c.supp.Finite} = 1 := by
  obtain ⟨e⟩ := jed_faithfulDiscreteJordan (walkSubgraph d hclosed hsimple)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin,
    walkSubgraph_nullity_one d hclosed hsimple]

/-- The ray-parity interior of the walk coincides with the union of bounded face components. Not
  used in this development; the corresponding statement is proved as
  `StatMech.Onsager.WalkCellRegion.mem_interiorCells_iff_rayParity` for walks without right
  turns. -/
def BridgeParityMembership {m : ℕ} (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d)) : Prop :=
  ∀ a b : ℤ, rayParity d a b = 1 ↔
    ((whb_faceRegion (imageGraph (walkSubgraph d hclosed hsimple))).connectedComponentMk
      ![a, b]).supp.Finite

/-- Adjacency in the face graph of the walk is the absence of a walk step on the common side of two
  cells. Not used in this development. -/
def BridgeAdjacencyClimb {m : ℕ} (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d)) : Prop :=
  ∀ a b : ℤ,
    ((whb_faceRegion (imageGraph (walkSubgraph d hclosed hsimple))).Adj ![a, b] ![a + 1, b] ↔
      (∀ k : Fin (m + 3), isVertEdge (d k) → (pos d k).1 = a + 1 →
        ¬ (min ((pos d k).2) ((pos d (k + 1)).2) ≤ b ∧
           b < max ((pos d k).2) ((pos d (k + 1)).2)))) ∧
    ((whb_faceRegion (imageGraph (walkSubgraph d hclosed hsimple))).Adj ![a, b] ![a, b + 1] ↔
      (∀ k : Fin (m + 3), isHorizEdge (d k) →
        min ((pos d k).1) ((pos d (k + 1)).1) = a → (pos d k).2 ≠ b + 1))

end StatMech.Onsager.JedBridge
