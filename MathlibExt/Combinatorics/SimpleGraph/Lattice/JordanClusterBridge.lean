/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanEnclosureDuality
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.NoPinchMatching
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.StarHull

/-!
# Bounded regions of lattice cycles

By the discrete Jordan–Euler theorem, the number of bounded regions of a finite subgraph of `ℤ²` is
its cycle rank. A connected graph with as many edges as vertices has cycle rank one, so it has
exactly one bounded region: the lattice Jordan curve theorem for simple cycles. The unit square and
an L-shaped 8-cycle are examples. The two-site set `{(0, 0), (1, 1)}` is not king-saturated and is
not its own star hull.

## Main definitions

* `StatMech.Lattice.jcb_BoundedRegion P`: the bounded components of the face-region graph of `P`.
* `StatMech.Lattice.jcb_boundedRegionEquiv P`: their bijection with `Fin (nullity P.G)`.
* `StatMech.Lattice.jcb_uniqueBoundedRegion_of_connected_cycle`: a connected `P` with `|E| = |V|`
  has a unique bounded region.
* `StatMech.Lattice.jcb_Lemb`, `StatMech.Lattice.jcb_Lcyc`, `StatMech.Lattice.jcb_LPce`: an 8-cycle
  around the L-shaped tromino.
* `StatMech.Lattice.jcb_diagK`: the set `{(0, 0), (1, 1)}`.

## Main results

* `StatMech.Lattice.jcb_boundedRegion_card_eq_nullity`: the number of bounded regions is the cycle
  rank.
* `StatMech.Lattice.jcb_nullity_eq_one_of_connected_card_eq`: connected with `|E| = |V|` gives cycle
  rank one.
* `StatMech.Lattice.jcb_square_uniqueBoundedRegion`,
  `StatMech.Lattice.jcb_Lshape_uniqueBoundedRegion`: the unit square and the L-shaped cycle have one
  bounded region each.
-/

@[expose] public section

open SimpleGraph Set

namespace StatMech

namespace Lattice

/-- The bounded (finite) connected components of the face-region graph of `P`. -/
abbrev jcb_BoundedRegion (P : PlanarZ2Subgraph) : Type :=
  {c : (whb_faceRegion (imageGraph P)).ConnectedComponent // c.supp.Finite}

/-- The bijection between bounded regions of `P` and `Fin (nullity P.G)` given by the discrete
Jordan–Euler theorem. -/
noncomputable def jcb_boundedRegionEquiv (P : PlanarZ2Subgraph) :
    jcb_BoundedRegion P ≃ Fin (nullity P.G) :=
  (jed_faithfulDiscreteJordan P).some

theorem jcb_boundedRegion_card_eq_nullity (P : PlanarZ2Subgraph) :
    Nat.card (jcb_BoundedRegion P) = nullity P.G := by
  rw [Nat.card_eq_of_bijective _ (jcb_boundedRegionEquiv P).bijective, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem jcb_nullity_eq_one_of_connected_card_eq {V : Type} [Finite V] (G : SimpleGraph V)
    (hconn : G.Connected) (hcard : G.edgeSet.ncard = Nat.card V) :
    nullity G = 1 := by
  classical
  have hbound := card_le_edgeSet_add_components G
  have hcomp : Nat.card G.ConnectedComponent = 1 := card_components_eq_one_of_connected hconn
  unfold nullity
  rw [hcard, hcomp]
  have hpos : 0 < Nat.card V := by
    have : Nonempty V := hconn.nonempty
    exact Nat.card_pos
  omega

/-- A `PlanarZ2Subgraph` has finitely many bounded regions. -/
noncomputable instance jcb_boundedRegion_finite (P : PlanarZ2Subgraph) :
    Finite (jcb_BoundedRegion P) := by
  have : Finite (whb_faceRegion (imageGraph P)).ConnectedComponent :=
    jfc_whb_regionComponents_finite (imageGraph P) (Set.toFinite (imageGraph P).edgeSet)
  infer_instance

/-- A `PlanarZ2Subgraph` of cycle rank one has exactly one bounded region. -/
@[reducible] noncomputable def jcb_uniqueBoundedRegion_of_nullity_one (P : PlanarZ2Subgraph)
    (h1 : nullity P.G = 1) : Unique (jcb_BoundedRegion P) := by
  have hcard : Nat.card (jcb_BoundedRegion P) = 1 := by
    rw [jcb_boundedRegion_card_eq_nullity, h1]
  obtain ⟨hsub, hne⟩ := Nat.card_eq_one_iff_unique.mp hcard
  exact ⟨⟨hne.some⟩, fun a => hsub.elim a hne.some⟩

theorem jcb_boundedRegion_card_eq_one_of_nullity_one (P : PlanarZ2Subgraph)
    (h1 : nullity P.G = 1) : Nat.card (jcb_BoundedRegion P) = 1 := by
  rw [jcb_boundedRegion_card_eq_nullity, h1]

/-- **Jordan curve theorem** for lattice cycles: a connected `PlanarZ2Subgraph` with as many
edges as vertices has exactly one bounded region. Reference: C. Jordan, *Cours d'analyse*
(1887); for the discrete form, C. Thomassen, *The Jordan–Schönflies theorem and the
classification of surfaces* (1992). -/
@[reducible] noncomputable def jcb_uniqueBoundedRegion_of_connected_cycle (P : PlanarZ2Subgraph)
    (hconn : P.G.Connected) (hcard : P.G.edgeSet.ncard = Nat.card P.V) :
    Unique (jcb_BoundedRegion P) :=
  jcb_uniqueBoundedRegion_of_nullity_one P
    (jcb_nullity_eq_one_of_connected_card_eq P.G hconn hcard)

/-- Adjacency of the 4-cycle is decidable. -/
instance jcb_cyc4_decAdj : DecidableRel jbc_cyc4.Adj := fun i j => by
  rw [jbc_cyc4_adj]; infer_instance

theorem jcb_cyc4_edge_card : jbc_cyc4.edgeSet.ncard = 4 := by
  rw [Set.ncard_eq_toFinset_card']; decide

theorem jcb_cyc4_connected : jbc_cyc4.Connected := by
  rw [connected_iff]
  refine ⟨?_, ⟨0⟩⟩
  have h01 : jbc_cyc4.Reachable 0 1 := (show jbc_cyc4.Adj 0 1 by decide).reachable
  have h03 : jbc_cyc4.Reachable 0 3 := (show jbc_cyc4.Adj 0 3 by decide).reachable
  have h32 : jbc_cyc4.Reachable 3 2 := (show jbc_cyc4.Adj 3 2 by decide).reachable
  have h02 : jbc_cyc4.Reachable 0 2 := h03.trans h32
  intro i j
  fin_cases i <;> fin_cases j <;>
    first
      | exact Reachable.refl _
      | exact h01 | exact h01.symm | exact h02 | exact h02.symm | exact h03 | exact h03.symm
      | exact h01.symm.trans h02 | exact h02.symm.trans h01
      | exact h01.symm.trans h03 | exact h03.symm.trans h01
      | exact h02.symm.trans h03 | exact h03.symm.trans h02

theorem jcb_square_nullity_one : nullity jbc_Pce.G = 1 := by
  refine jcb_nullity_eq_one_of_connected_card_eq jbc_Pce.G jcb_cyc4_connected ?_
  change jbc_cyc4.edgeSet.ncard = Nat.card (Fin 4)
  rw [jcb_cyc4_edge_card, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem jcb_square_uniqueBoundedRegion : Nat.card (jcb_BoundedRegion jbc_Pce) = 1 :=
  jcb_boundedRegion_card_eq_one_of_nullity_one jbc_Pce jcb_square_nullity_one

/-- The eight lattice points around the L-shaped tromino, in cyclic order. -/
def jcb_Lemb (i : Fin 8) : Site 2 :=
  match i with
  | 0 => ![0, 0] | 1 => ![1, 0] | 2 => ![2, 0] | 3 => ![2, 1]
  | 4 => ![1, 1] | 5 => ![1, 2] | 6 => ![0, 2] | 7 => ![0, 1]

theorem jcb_Lemb_inj : Function.Injective jcb_Lemb := by decide +kernel

/-- Adjacency of the 8-cycle on `Fin 8`, as a Boolean relation. -/
def jcb_LcycRel (i j : Fin 8) : Bool := (i + 1 == j) || (j + 1 == i)

/-- The 8-cycle on `Fin 8`. -/
def jcb_Lcyc : SimpleGraph (Fin 8) where
  Adj i j := jcb_LcycRel i j
  symm := ⟨by intro i j h; revert h; revert i j; decide⟩
  loopless := ⟨by intro i h; revert h; revert i; decide⟩

@[simp] theorem jcb_Lcyc_adj (i j : Fin 8) : jcb_Lcyc.Adj i j ↔ jcb_LcycRel i j := Iff.rfl

/-- Adjacency of the 8-cycle is decidable. -/
instance jcb_Lcyc_decAdj : DecidableRel jcb_Lcyc.Adj := fun i j => by
  rw [jcb_Lcyc_adj]; infer_instance

theorem jcb_Lemb_isSub :
    ∀ ⦃i j : Fin 8⦄, jcb_Lcyc.Adj i j → (hypercubicLattice 2).Adj (jcb_Lemb i) (jcb_Lemb j) := by
  intro i j h
  rw [jcb_Lcyc_adj] at h
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  revert h; fin_cases i <;> fin_cases j <;> simp [jcb_LcycRel, jcb_Lemb]

/-- The 8-cycle around the L-shaped tromino as a `PlanarZ2Subgraph`. -/
noncomputable def jcb_LPce : PlanarZ2Subgraph where
  V := Fin 8
  finV := inferInstance
  decV := inferInstance
  G := jcb_Lcyc
  emb := ⟨jcb_Lemb, jcb_Lemb_inj⟩
  isSub := jcb_Lemb_isSub

theorem jcb_Lcyc_edge_card : jcb_Lcyc.edgeSet.ncard = 8 := by
  rw [Set.ncard_eq_toFinset_card']; decide

theorem jcb_Lcyc_connected : jcb_Lcyc.Connected := by
  rw [connected_iff]
  refine ⟨?_, ⟨0⟩⟩
  have step : ∀ i : Fin 8, jcb_Lcyc.Reachable 0 i := by
    have r01 : jcb_Lcyc.Adj 0 1 := by decide
    have r12 : jcb_Lcyc.Adj 1 2 := by decide
    have r23 : jcb_Lcyc.Adj 2 3 := by decide
    have r34 : jcb_Lcyc.Adj 3 4 := by decide
    have r45 : jcb_Lcyc.Adj 4 5 := by decide
    have r56 : jcb_Lcyc.Adj 5 6 := by decide
    have r67 : jcb_Lcyc.Adj 6 7 := by decide
    intro i
    fin_cases i
    · exact Reachable.refl _
    · exact r01.reachable
    · exact r01.reachable.trans r12.reachable
    · exact r01.reachable.trans (r12.reachable.trans r23.reachable)
    · exact r01.reachable.trans (r12.reachable.trans (r23.reachable.trans r34.reachable))
    · exact r01.reachable.trans (r12.reachable.trans (r23.reachable.trans
        (r34.reachable.trans r45.reachable)))
    · exact r01.reachable.trans (r12.reachable.trans (r23.reachable.trans
        (r34.reachable.trans (r45.reachable.trans r56.reachable))))
    · exact r01.reachable.trans (r12.reachable.trans (r23.reachable.trans
        (r34.reachable.trans (r45.reachable.trans (r56.reachable.trans r67.reachable)))))
  intro i j
  exact (step i).symm.trans (step j)

theorem jcb_Lshape_nullity_one : nullity jcb_LPce.G = 1 := by
  refine jcb_nullity_eq_one_of_connected_card_eq jcb_LPce.G jcb_Lcyc_connected ?_
  change jcb_Lcyc.edgeSet.ncard = Nat.card (Fin 8)
  rw [jcb_Lcyc_edge_card, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem jcb_Lshape_uniqueBoundedRegion : Nat.card (jcb_BoundedRegion jcb_LPce) = 1 :=
  jcb_boundedRegion_card_eq_one_of_nullity_one jcb_LPce jcb_Lshape_nullity_one

/-- The two-site set `{(0, 0), (1, 1)}`, which touches diagonally. -/
def jcb_diagK : Set (Site 2) := {![0, 0], ![1, 1]}

theorem jcb_diagK_not_kingSat : ¬ npm_KingSaturated jcb_diagK := by
  intro h
  have hc := (h ![0, 0]).1
  simp only [npd_P00, npd_P11, npd_P10, npd_P01,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hc
  have h00 : (![(0:ℤ), 0] : Site 2) ∈ jcb_diagK := Or.inl rfl
  have h11 : (![(0:ℤ) + 1, 0 + 1] : Site 2) ∈ jcb_diagK := by
    right; rw [Set.mem_singleton_iff, site2_eq]; norm_num
  rcases hc h00 h11 with h10 | h01
  · rw [jcb_diagK, Set.mem_insert_iff, Set.mem_singleton_iff, site2_eq, site2_eq] at h10; omega
  · rw [jcb_diagK, Set.mem_insert_iff, Set.mem_singleton_iff, site2_eq, site2_eq] at h01; omega

theorem jcb_diagK_not_own_starHull : ndt_StarHull jcb_diagK ≠ jcb_diagK := by
  intro heq
  exact jcb_diagK_not_kingSat (heq ▸ ndt_kingSaturated_starHull jcb_diagK)

theorem jcb_status :
    (∀ P : PlanarZ2Subgraph, Nat.card (jcb_BoundedRegion P) = nullity P.G) ∧
    (∀ P : PlanarZ2Subgraph, nullity P.G = 1 → Nat.card (jcb_BoundedRegion P) = 1) ∧
    Nat.card (jcb_BoundedRegion jbc_Pce) = 1 ∧
    Nat.card (jcb_BoundedRegion jcb_LPce) = 1 ∧
    ndt_StarHull jcb_diagK ≠ jcb_diagK :=
  ⟨jcb_boundedRegion_card_eq_nullity, jcb_boundedRegion_card_eq_one_of_nullity_one,
    jcb_square_uniqueBoundedRegion, jcb_Lshape_uniqueBoundedRegion, jcb_diagK_not_own_starHull⟩

end Lattice

end StatMech
