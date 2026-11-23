/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanEnclosureDuality

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanEnclosureDuality`

Applies the unconditional discrete Jordan curve theorem `jed_faithfulDiscreteJordan` (for every
finite subgraph `P` of `ℤ²`, the bounded faces of `P` are in bijection with `Fin (nullity P.G)`)
to three embedded graphs and reads off the number of bounded faces:
* the unit square `(0,0) - (1,0) - (1,1) - (0,1) - (0,0)`: nullity one, so exactly one bounded
  face;
* the domino `2 × 1` with its middle edge (two unit squares sharing an edge): nullity two, so two
  bounded faces;
* the straight path `(0,0) - (1,0) - (2,0)`: nullity zero, so no bounded face.
The nullities are computed from edge counts (`decide`) and connectivity.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.JordanEnclosureDuality

open _root_.StatMech _root_.StatMech.Lattice _root_.SimpleGraph

/-- A connected graph has exactly one component. -/
theorem card_components_of_connected {V : Type*} {G : SimpleGraph V} (h : G.Connected) :
    Nat.card G.ConnectedComponent = 1 := by
  have := h.preconnected.subsingleton_connectedComponent
  exact Nat.card_of_subsingleton (G.connectedComponentMk h.nonempty.some)

/-- A graph on `Fin n` given by a symmetric irreflexive Boolean relation. -/
def ofRel {n : ℕ} (r : Fin n → Fin n → Bool) (hs : ∀ i j, r i j = r j i)
    (hl : ∀ i, r i i = false) : SimpleGraph (Fin n) where
  Adj i j := r i j
  symm := ⟨fun i j h => by rwa [hs]⟩
  loopless := ⟨fun i h => by simp [hl] at h⟩

instance {n : ℕ} (r : Fin n → Fin n → Bool) (hs) (hl) : DecidableRel (ofRel r hs hl).Adj :=
  fun i j => inferInstanceAs (Decidable (r i j = true))

/-- The 4-cycle `0 - 1 - 2 - 3 - 0`. -/
abbrev cyc4 : SimpleGraph (Fin 4) :=
  ofRel (fun i j => (j = i + 1) || (i = j + 1)) (by decide) (by decide)

/-- The corners of the unit square, in cyclic order. -/
def sqEmb : Fin 4 → Site 2 := ![![0, 0], ![1, 0], ![1, 1], ![0, 1]]

/-- The unit square of `ℤ²` as a planar subgraph. -/
def unitSquare : PlanarZ2Subgraph where
  V := Fin 4
  finV := inferInstance
  decV := inferInstance
  G := cyc4
  emb := ⟨sqEmb, by decide +kernel⟩
  isSub := by
    intro i j h
    change ((fun i j : Fin 4 => (j = i + 1) || (i = j + 1)) i j) = true at h
    rw [hypercubicLattice_adj, Fin.sum_univ_two]
    revert h; fin_cases i <;> fin_cases j <;> simp [sqEmb]

theorem nullity_unitSquare : nullity unitSquare.G = 1 := by
  change nullity cyc4 = 1
  have hc : cyc4.Connected := by
    have a : ∀ i : Fin 4, cyc4.Adj i (i + 1) := by decide
    refine (connected_iff_exists_forall_reachable _).mpr ⟨0, fun i => ?_⟩
    fin_cases i
    · rfl
    · exact (a 0).reachable
    · exact (a 0).reachable.trans (a 1).reachable
    · exact (a 3).symm.reachable
  have he : cyc4.edgeSet.ncard = 4 := by
    rw [Set.ncard_eq_toFinset_card']; decide
  unfold nullity
  rw [he, card_components_of_connected hc]
  simp

-- The unit square has exactly one bounded face.
example : Nat.card {c : (whb_faceRegion (imageGraph unitSquare)).ConnectedComponent //
    c.supp.Finite} = 1 := by
  obtain ⟨e⟩ := jed_faithfulDiscreteJordan unitSquare
  rw [Nat.card_congr e, nullity_unitSquare, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- The domino: the 6-cycle `0 - 1 - 2 - 3 - 4 - 5 - 0` plus the chord `1 - 4`. -/
abbrev domino : SimpleGraph (Fin 6) :=
  ofRel (fun i j => (j = i + 1) || (i = j + 1) || (i = 1 && j = 4) || (i = 4 && j = 1))
    (by decide) (by decide)

/-- The sites of the `2 × 1` domino, around its boundary. -/
def domEmb : Fin 6 → Site 2 := ![![0, 0], ![1, 0], ![2, 0], ![2, 1], ![1, 1], ![0, 1]]

/-- Two unit squares sharing the edge `(1,0) - (1,1)`, as a planar subgraph. -/
def dominoP : PlanarZ2Subgraph where
  V := Fin 6
  finV := inferInstance
  decV := inferInstance
  G := domino
  emb := ⟨domEmb, by decide +kernel⟩
  isSub := by
    intro i j h
    change ((fun i j : Fin 6 => (j = i + 1) || (i = j + 1) || (i = 1 && j = 4) ||
      (i = 4 && j = 1)) i j) = true at h
    rw [hypercubicLattice_adj, Fin.sum_univ_two]
    revert h; fin_cases i <;> fin_cases j <;> simp [domEmb]

theorem nullity_dominoP : nullity dominoP.G = 2 := by
  change nullity domino = 2
  have hc : domino.Connected := by
    have a : ∀ i : Fin 6, domino.Adj i (i + 1) := by decide
    have r1 : domino.Reachable 0 1 := (a 0).reachable
    have r2 : domino.Reachable 0 2 := r1.trans (a 1).reachable
    have r3 : domino.Reachable 0 3 := r2.trans (a 2).reachable
    have r4 : domino.Reachable 0 4 := r3.trans (a 3).reachable
    have r5 : domino.Reachable 0 5 := r4.trans (a 4).reachable
    refine (connected_iff_exists_forall_reachable _).mpr ⟨0, fun i => ?_⟩
    fin_cases i
    exacts [Reachable.refl _, r1, r2, r3, r4, r5]
  have he : domino.edgeSet.ncard = 7 := by
    rw [Set.ncard_eq_toFinset_card']; decide
  unfold nullity
  rw [he, card_components_of_connected hc]
  simp

-- The domino has exactly two bounded faces.
example : Nat.card {c : (whb_faceRegion (imageGraph dominoP)).ConnectedComponent //
    c.supp.Finite} = 2 := by
  obtain ⟨e⟩ := jed_faithfulDiscreteJordan dominoP
  rw [Nat.card_congr e, nullity_dominoP, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- The path `0 - 1 - 2`. -/
abbrev path3 : SimpleGraph (Fin 3) :=
  ofRel (fun i j => (i.val + 1 = j.val) || (j.val + 1 = i.val)) (by decide) (by decide)

/-- The straight path `(0,0) - (1,0) - (2,0)` as a planar subgraph. -/
def pathP : PlanarZ2Subgraph where
  V := Fin 3
  finV := inferInstance
  decV := inferInstance
  G := path3
  emb := ⟨![![0, 0], ![1, 0], ![2, 0]], by decide +kernel⟩
  isSub := by
    intro i j h
    change ((fun i j : Fin 3 => (i.val + 1 = j.val) || (j.val + 1 = i.val)) i j) = true at h
    rw [hypercubicLattice_adj, Fin.sum_univ_two]
    revert h; fin_cases i <;> fin_cases j <;> simp

theorem nullity_pathP : nullity pathP.G = 0 := by
  change nullity path3 = 0
  have hc : path3.Connected := by
    have a01 : path3.Adj 0 1 := by decide
    have a12 : path3.Adj 1 2 := by decide
    refine (connected_iff_exists_forall_reachable _).mpr ⟨0, fun i => ?_⟩
    fin_cases i
    · rfl
    · exact a01.reachable
    · exact a01.reachable.trans a12.reachable
  have he : path3.edgeSet.ncard = 2 := by
    rw [Set.ncard_eq_toFinset_card']; decide
  unfold nullity
  rw [he, card_components_of_connected hc]
  simp

-- A path encloses no bounded face.
example : IsEmpty {c : (whb_faceRegion (imageGraph pathP)).ConnectedComponent //
    c.supp.Finite} := by
  obtain ⟨e⟩ := jed_faithfulDiscreteJordan pathP
  rw [nullity_pathP] at e
  exact e.isEmpty

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.JordanEnclosureDuality
