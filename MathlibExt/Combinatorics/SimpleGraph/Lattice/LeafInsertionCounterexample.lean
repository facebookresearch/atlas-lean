/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.ReachesExteriorConnected

/-!
# Inserting a site can disconnect the complement

The leaf-insertion property `arcns_LeafRemovable S u'` (connectivity of the complement of `S`
survives adding `u'`) fails in general. Take the seven sites

  `(1, 1), (0, 1), (-1, 1), (-1, 0), (-1, -1), (0, -1), (1, -1)`

surrounding the origin except for the gap `(1, 0)`. Their complement is connected, but adding the
gap site `(1, 0)` isolates the origin. Since the seven sites form a self-avoiding walk starting
next to `(1, 0)`, the hypothesis "every leaf insertion along every arc is removable" is false
as well.

## Main definitions

* `StatMech.Lattice.lrc_ringS`: the eight sites around the origin minus the gap `(1, 0)`.
* `StatMech.Lattice.lrc_uPrime`: the gap site `(1, 0)`.

## Main results

* `StatMech.Lattice.lrc_ring_connected`: the complement of the open ring is connected.
* `StatMech.Lattice.lrc_insert_not_connected`: the complement of the closed ring is not
  connected (the origin is cut off).
* `StatMech.Lattice.lrc_leafRemovable_false`: `arcns_LeafRemovable lrc_ringS lrc_uPrime` fails.
* `StatMech.Lattice.lrc_arc_leafHypothesis_false`: the leaf-insertion hypothesis for all arcs
  is false.
* `StatMech.Lattice.lrc_leafRemovable_of_reachesFarLeft`: a sufficient condition for leaf
  insertion through the far-left half-plane.
-/

@[expose] public section

open Set SimpleGraph

namespace StatMech

namespace Lattice

/-- A site left of every site of `S` is not in `S`. -/
theorem lrc_farLeft_offS {S : Set (Site 2)} {b : ℤ} (hb : ∀ q ∈ S, b ≤ q 0)
    {z : Site 2} (hz : z 0 ≤ b - 1) : z ∉ S := by
  intro hzS
  have := hb z hzS
  omega

/-- If the complement of `S` is connected and `S` lies right of column `b`, every site off `S`
reaches `(b - 1, x 1)` avoiding `S`. -/
theorem lrc_reachesFarLeft_offS {S : Set (Site 2)} (hS : arcns_OffSupportConnected S)
    {b : ℤ} (hb : ∀ q ∈ S, b ≤ q 0) {x : Site 2} (hx : x ∉ S) :
    ∃ p : (hypercubicLattice 2).Walk x ![b - 1, x 1], (∀ w ∈ p.support, w ∉ S) := by
  have hc : (![b - 1, x 1] : Site 2) ∉ S :=
    lrc_farLeft_offS hb (z := ![b - 1, x 1]) (by simp)
  exact arcns_walk_of_connected hS hx hc

/-- The eight sites around the origin with the gap `(1, 0)` left open; as a walk from `(1, 1)` to
`(1, -1)` through the left side it is an arc. -/
def lrc_ringS : Set (Site 2) :=
  {![1, 1], ![1, -1], ![0, 1], ![0, -1], ![-1, 1], ![-1, 0], ![-1, -1]}

/-- The gap site `(1, 0)` of `lrc_ringS`. -/
def lrc_uPrime : Site 2 := ![1, 0]

/-- Sites with a differing coordinate are distinct. -/
theorem lrc_cell_ne {a b c d : ℤ} (h : a ≠ c ∨ b ≠ d) : (![a, b] : Site 2) ≠ ![c, d] := by
  intro he
  rcases h with h | h
  · exact h (by have := congrFun he 0; simpa using this)
  · exact h (by have := congrFun he 1; simpa using this)

theorem lrc_uPrime_not_mem : lrc_uPrime ∉ lrc_ringS := by
  simp only [lrc_uPrime, lrc_ringS, Set.mem_insert_iff, Set.mem_singleton_iff]
  push Not
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply lrc_cell_ne <;> omega

theorem lrc_origin_neighbours_in_barrier :
    (![1, 0] : Site 2) ∈ insert lrc_uPrime lrc_ringS ∧
    (![-1, 0] : Site 2) ∈ insert lrc_uPrime lrc_ringS ∧
    (![0, 1] : Site 2) ∈ insert lrc_uPrime lrc_ringS ∧
    (![0, -1] : Site 2) ∈ insert lrc_uPrime lrc_ringS := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp only [lrc_uPrime, lrc_ringS, Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

theorem lrc_origin_off_barrier : (![0, 0] : Site 2) ∉ insert lrc_uPrime lrc_ringS := by
  simp only [lrc_uPrime, lrc_ringS, Set.mem_insert_iff, Set.mem_singleton_iff]
  push Not
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply lrc_cell_ne <;> omega

theorem lrc_east_off_barrier : (![2, 0] : Site 2) ∉ insert lrc_uPrime lrc_ringS := by
  simp only [lrc_uPrime, lrc_ringS, Set.mem_insert_iff, Set.mem_singleton_iff]
  push Not
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply lrc_cell_ne <;> omega

theorem lrc_adj_origin_cases {z : Site 2} (h : (hypercubicLattice 2).Adj ![0, 0] z) :
    z = ![1, 0] ∨ z = ![-1, 0] ∨ z = ![0, 1] ∨ z = ![0, -1] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  have hez : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
  have : (z 0 = 1 ∧ z 1 = 0) ∨ (z 0 = -1 ∧ z 1 = 0) ∨
      (z 0 = 0 ∧ z 1 = 1) ∨ (z 0 = 0 ∧ z 1 = -1) := by omega
  rcases this with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;>
    [ (left); (right; left); (right; right; left); (right; right; right) ] <;>
    · rw [hez, a, b]

/-- With the closed ring removed, the origin has no neighbour. -/
theorem lrc_origin_isolated {z : Site 2} :
    ¬ (ffc_offSupportLattice (insert lrc_uPrime lrc_ringS)).Adj ![0, 0] z := by
  rw [ffc_offSupportLattice_adj]
  rintro ⟨hadj, _, hz⟩
  obtain ⟨h1, h2, h3, h4⟩ := lrc_origin_neighbours_in_barrier
  rcases lrc_adj_origin_cases hadj with rfl | rfl | rfl | rfl
  · exact hz h1
  · exact hz h2
  · exact hz h3
  · exact hz h4

/-- A walk from an isolated vertex (`G.IsIsolated a`) is trivial: its endpoint is `a`. -/
theorem lrc_eq_of_walk_from_isolated {V : Type*} {G : SimpleGraph V} {a b : V}
    (w : G.Walk a b) (hiso : ∀ z, ¬ G.Adj a z) : a = b := by
  cases w with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (hiso _)

theorem lrc_origin_not_reachable_east :
    ¬ (ffc_offSupportLattice (insert lrc_uPrime lrc_ringS)).Reachable ![0, 0] ![2, 0] := by
  rintro ⟨w⟩
  have hne : (![0, 0] : Site 2) ≠ ![2, 0] := lrc_cell_ne (by left; omega)
  exact hne (lrc_eq_of_walk_from_isolated w (fun z => lrc_origin_isolated))

/-- The complement of the closed ring `insert lrc_uPrime lrc_ringS` is not connected: the origin
cannot reach `(2, 0)`. -/
theorem lrc_insert_not_connected :
    ¬ arcns_OffSupportConnected (insert lrc_uPrime lrc_ringS) := by
  intro hconn
  exact lrc_origin_not_reachable_east
    (hconn ![0, 0] ![2, 0] lrc_origin_off_barrier lrc_east_off_barrier)

theorem lrc_ringS_subset_box : lrc_ringS ⊆ box 2 1 := by
  intro z hz
  simp only [lrc_ringS, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rw [mem_box]
  intro i
  fin_cases i <;>
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem lrc_box_off_ring_cases {z : Site 2} (hbox : z ∈ box 2 1) (hoff : z ∉ lrc_ringS) :
    z = ![0, 0] ∨ z = ![1, 0] := by
  rw [mem_box] at hbox
  have h0 := hbox 0
  have h1 := hbox 1
  have hc0 : z 0 = -1 ∨ z 0 = 0 ∨ z 0 = 1 := by omega
  have hc1 : z 1 = -1 ∨ z 1 = 0 ∨ z 1 = 1 := by omega
  have hez : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
  simp only [lrc_ringS, Set.mem_insert_iff, Set.mem_singleton_iff] at hoff
  push Not at hoff
  obtain ⟨n11, n1m1, n01, n0m1, nm11, nm10, nm1m1⟩ := hoff
  have mk : ∀ a b : ℤ, z 0 = a → z 1 = b → z = ![a, b] := by
    intro a b ha hb; rw [hez, ha, hb]
  rcases hc0 with e0 | e0 | e0 <;> rcases hc1 with e1 | e1 | e1 <;>
    first
      | (left; exact mk _ _ e0 e1)
      | (right; exact mk _ _ e0 e1)
      | (exfalso; first
          | (exact n11 (mk _ _ e0 e1)) | (exact n1m1 (mk _ _ e0 e1))
          | (exact n01 (mk _ _ e0 e1)) | (exact n0m1 (mk _ _ e0 e1))
          | (exact nm11 (mk _ _ e0 e1)) | (exact nm10 (mk _ _ e0 e1))
          | (exact nm1m1 (mk _ _ e0 e1)))

theorem lrc_row0_clear {c t : ℤ} (hc : 0 ≤ c) (ht : t ∈ Set.uIcc c (1 + 1 : ℤ)) :
    (![t, 0] : Site 2) ∉ lrc_ringS := by
  rw [Set.mem_uIcc] at ht
  have htge : 0 ≤ t := by omega
  simp only [lrc_ringS, Set.mem_insert_iff, Set.mem_singleton_iff]
  push Not
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply lrc_cell_ne <;> omega

theorem lrc_origin_reachesExterior :
    ∃ (e : Site 2) (p : (hypercubicLattice 2).Walk ![0, 0] e),
      (∀ w ∈ p.support, w ∉ lrc_ringS) ∧ e ∈ exterior 2 1 := by
  refine arcxc_reachesExterior_of_rowClear (z := ![0, 0]) ?_
  intro t ht hmem
  simp only [Matrix.cons_val_zero] at ht
  exact lrc_row0_clear (by norm_num) ht hmem

theorem lrc_gap_reachesExterior :
    ∃ (e : Site 2) (p : (hypercubicLattice 2).Walk ![1, 0] e),
      (∀ w ∈ p.support, w ∉ lrc_ringS) ∧ e ∈ exterior 2 1 := by
  refine arcxc_reachesExterior_of_rowClear (z := ![1, 0]) ?_
  intro t ht hmem
  simp only [Matrix.cons_val_zero] at ht
  exact lrc_row0_clear (by norm_num) ht hmem

theorem lrc_ring_reachesExterior : arcxc_ReachesExterior lrc_ringS 1 := by
  refine ⟨lrc_ringS_subset_box, ?_⟩
  intro x hx
  by_cases hbox : x ∈ box 2 1
  · rcases lrc_box_off_ring_cases hbox hx with rfl | rfl
    · exact lrc_origin_reachesExterior
    · exact lrc_gap_reachesExterior
  · have hxext : x ∈ exterior 2 1 := by
      rw [exterior_eq_compl_box]; exact hbox
    exact ⟨x, SimpleGraph.Walk.nil, by
      intro w hw; rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw; exact hw ▸ hx,
      hxext⟩

/-- The complement of the open ring `lrc_ringS` is connected: the origin leaves through the gap
`(1, 0)`. -/
theorem lrc_ring_connected : arcns_OffSupportConnected lrc_ringS :=
  arcxc_connected_of_reachesExterior lrc_ring_reachesExterior

/-- Leaf insertion fails for the open ring and its gap site: inserting `(1, 0)` into `lrc_ringS`
disconnects the complement. -/
theorem lrc_leafRemovable_false :
    ¬ arcns_LeafRemovable lrc_ringS lrc_uPrime := by
  intro hres
  exact lrc_insert_not_connected (hres lrc_ring_connected)

/-- Two sites `(a, b)` and `(c, d)` with `|a - c| + |b - d| = 1` are adjacent. -/
theorem lrc_adj_of_natAbs {a b c d : ℤ} (h : (a - c).natAbs + (b - d).natAbs = 1) :
    (hypercubicLattice 2).Adj ![a, b] ![c, d] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  simpa using h

/-- The leaf-insertion hypothesis for arcs is false: it is not true that for every self-avoiding
walk `cons h q` from `a`, adding `a` to the support of `q` keeps the complement connected. The
witness is the walk from `(1, 0)` around the ring `lrc_ringS` from `(1, 1)` to `(1, -1)`; adding
`(1, 0)` closes the ring and isolates the origin (`lrc_leafRemovable_false`). An induction over
arcs that assumes this hypothesis therefore proves nothing. -/
theorem lrc_arc_leafHypothesis_false :
    ¬ (∀ (a b c : Site 2) (h : (hypercubicLattice 2).Adj a b)
      (q : (hypercubicLattice 2).Walk b c), (Walk.cons h q).IsPath →
        arcns_LeafRemovable {z : Site 2 | z ∈ q.support} a) := by
  intro hleaf
  let q : (hypercubicLattice 2).Walk ![1, 1] ![1, -1] :=
    Walk.cons (lrc_adj_of_natAbs (by norm_num) : (hypercubicLattice 2).Adj ![1, 1] ![0, 1]) <|
    Walk.cons (lrc_adj_of_natAbs (by norm_num) : (hypercubicLattice 2).Adj ![0, 1] ![-1, 1]) <|
    Walk.cons (lrc_adj_of_natAbs (by norm_num) : (hypercubicLattice 2).Adj ![-1, 1] ![-1, 0]) <|
    Walk.cons (lrc_adj_of_natAbs (by norm_num) : (hypercubicLattice 2).Adj ![-1, 0] ![-1, -1]) <|
    Walk.cons (lrc_adj_of_natAbs (by norm_num) : (hypercubicLattice 2).Adj ![-1, -1] ![0, -1]) <|
    Walk.cons (lrc_adj_of_natAbs (by norm_num) : (hypercubicLattice 2).Adj ![0, -1] ![1, -1])
      Walk.nil
  have h0 : (hypercubicLattice 2).Adj lrc_uPrime ![1, 1] := lrc_adj_of_natAbs (by norm_num)
  have hpath : (Walk.cons h0 q).IsPath := by
    rw [Walk.isPath_def]
    have hs : (Walk.cons h0 q).support =
        [![1, 0], ![1, 1], ![0, 1], ![-1, 1], ![-1, 0], ![-1, -1], ![0, -1], ![1, -1]] := rfl
    rw [hs]
    simp [funext_iff, Fin.forall_fin_two]
  have hsupp : {z : Site 2 | z ∈ q.support} = lrc_ringS := by
    ext z
    have hs : q.support = [![1, 1], ![0, 1], ![-1, 1], ![-1, 0], ![-1, -1], ![0, -1], ![1, -1]] :=
      rfl
    rw [hs]
    simp only [Set.mem_ofPred_eq, List.mem_cons,
      List.not_mem_nil, or_false, lrc_ringS, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have := hleaf _ _ _ h0 q hpath
  rw [hsupp] at this
  exact lrc_leafRemovable_false this

/-- If `insert u' S` satisfies the far-left reachability criterion, adding `u'` to `S` keeps the
complement connected. -/
theorem lrc_leafRemovable_of_reachesFarLeft {S : Set (Site 2)} {u' : Site 2}
    (h : arcns_ReachesFarLeft (insert u' S)) : arcns_LeafRemovable S u' :=
  fun _ => arcns_connected_of_reachesFarLeft h

end Lattice

end StatMech
