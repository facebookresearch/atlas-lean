/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.FloodFillConnected
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.StraightWalk

/-!
# Connectivity of the lattice off a set of sites

For a set `B` of sites of the square lattice, `arcns_OffSupportConnected B` says that any two
sites outside `B` are joined by a lattice walk avoiding `B`, i.e. the lattice with `B` removed
(`ffc_offSupportLattice B`) is connected on the complement of `B`. This file gives a sufficient
criterion through the far-left half-plane and proves it for a single site.

It also introduces the leaf-insertion property `arcns_LeafRemovable S u'`: connectivity of the
complement of `S` survives adding the site `u'`. An induction along a self-avoiding walk would
derive connectivity of the complement of the walk (an arc) from this property at every step, but
the property fails in general: `StatMech.Lattice.lrc_leafRemovable_false` gives a seven-site arc
`S` and an adjacent site `u'` whose insertion encloses a site, and
`StatMech.Lattice.lrc_arc_leafHypothesis_false` shows that the induction hypothesis "every
leaf insertion along every arc is removable" is false. See `StatMech.Lattice.tnbp_RingChain` for
a local criterion that does work.

## Main definitions

* `StatMech.Lattice.arcns_OffSupportConnected B`: any two sites off `B` are joined by a walk
  avoiding `B`.
* `StatMech.Lattice.arcns_ReachesFarLeft B`: `B` lies right of a column `b`, and every site off
  `B` reaches the half-plane `x ≤ b - 1` by a walk avoiding `B`.
* `StatMech.Lattice.arcns_vlshape`: the L-shaped walk that runs vertically first, then
  horizontally.
* `StatMech.Lattice.arcns_LeafRemovable S u'`: if the complement of `S` is connected, so is the
  complement of `insert u' S`.

## Main results

* `StatMech.Lattice.arcns_offSupportConnected_iff_preconnected`: the predicate agrees with
  preconnectedness of the induced graph `(hypercubicLattice 2).induce Bᶜ`.
* `StatMech.Lattice.arcns_farLeft_connected`: two sites left of every site of `B` are joined by a
  walk avoiding `B`.
* `StatMech.Lattice.arcns_connected_of_reachesFarLeft`: `arcns_ReachesFarLeft B` implies
  `arcns_OffSupportConnected B`.
* `StatMech.Lattice.arcns_singlePoint_connected`: the square lattice minus one site is connected.

## Implementation notes

`ffc_offSupportLattice B` keeps every site and deletes the edges meeting `B`; the induced graph
`(hypercubicLattice 2).induce Bᶜ` is the same graph restricted to the vertex type `Bᶜ`.
-/

@[expose] public section

open Set SimpleGraph

namespace StatMech

namespace Lattice

/-- Any two sites outside `B` are connected in the square lattice with `B` removed. -/
def arcns_OffSupportConnected (B : Set (Site 2)) : Prop :=
  ∀ x y : Site 2, x ∉ B → y ∉ B → (ffc_offSupportLattice B).Reachable x y

/-- Under `arcns_OffSupportConnected B`, two sites off `B` are joined by a lattice walk whose
support avoids `B`. -/
theorem arcns_walk_of_connected {B : Set (Site 2)} (h : arcns_OffSupportConnected B)
    {x y : Site 2} (hx : x ∉ B) (hy : y ∉ B) :
    ∃ p : (hypercubicLattice 2).Walk x y, ∀ z ∈ p.support, z ∉ B :=
  (ffc_reachable_iff_offSupportWalk hx).mp (h x y hx hy)

/-- `arcns_OffSupportConnected B` says exactly that the induced subgraph of the square lattice on
the complement of `B` is preconnected. -/
theorem arcns_offSupportConnected_iff_preconnected (B : Set (Site 2)) :
    arcns_OffSupportConnected B ↔ ((hypercubicLattice 2).induce Bᶜ).Preconnected := by
  constructor
  · rintro h ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨p, hp⟩ := arcns_walk_of_connected h hx hy
    exact ⟨p.induce Bᶜ hp⟩
  · intro h x y hx hy
    let f : (hypercubicLattice 2).induce Bᶜ →g ffc_offSupportLattice B :=
      { toFun := Subtype.val, map_rel' := fun {a b} hab => ⟨hab, a.2, b.2⟩ }
    exact (h ⟨x, hx⟩ ⟨y, hy⟩).map f

/-- If every site of `B` has first coordinate at least `b`, any two sites in the half-plane
`x ≤ b - 1` are joined by an L-shaped walk avoiding `B`. -/
theorem arcns_farLeft_connected (B : Set (Site 2)) (b : ℤ) (hb : ∀ q ∈ B, b ≤ q 0)
    (z1 z2 : Site 2) (h1 : z1 0 ≤ b - 1) (h2 : z2 0 ≤ b - 1) :
    ∃ p : (hypercubicLattice 2).Walk z1 z2, ∀ w ∈ p.support, w ∉ B := by
  have e1 : (![z1 0, z1 1] : Site 2) = z1 := by funext i; fin_cases i <;> rfl
  have e2 : (![z2 0, z2 1] : Site 2) = z2 := by funext i; fin_cases i <;> rfl
  refine ⟨(sw_lshape (z1 0) (z1 1) (z2 0) (z2 1)).copy e1 e2, ?_⟩
  intro w hw hwB
  rw [Walk.support_copy, sw_lshape_support_eq] at hw
  have hbw : b ≤ w 0 := hb w hwB
  rcases hw with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · simp only [Matrix.cons_val_zero] at hbw
    rw [Set.mem_uIcc] at ht
    rcases ht with ⟨_, hle⟩ | ⟨_, hle⟩ <;> omega
  · simp only [Matrix.cons_val_zero] at hbw
    omega

/-- `B` lies to the right of a column `x = b`, and every site off `B` reaches the half-plane
`x ≤ b - 1` by a walk avoiding `B`. -/
def arcns_ReachesFarLeft (B : Set (Site 2)) : Prop :=
  ∃ b : ℤ, (∀ q ∈ B, b ≤ q 0) ∧
    ∀ x : Site 2, x ∉ B → ∃ (z0 : Site 2) (p : (hypercubicLattice 2).Walk x z0),
      (∀ w ∈ p.support, w ∉ B) ∧ z0 0 ≤ b - 1

/-- If every site off `B` reaches the far-left half-plane avoiding `B`, the complement of `B` is
connected. -/
theorem arcns_connected_of_reachesFarLeft {B : Set (Site 2)} (h : arcns_ReachesFarLeft B) :
    arcns_OffSupportConnected B := by
  obtain ⟨b, hb, hreach⟩ := h
  intro x y hx hy
  obtain ⟨zx, px, hpx, hzx⟩ := hreach x hx
  obtain ⟨zy, py, hpy, hzy⟩ := hreach y hy
  obtain ⟨pc, hpc⟩ := arcns_farLeft_connected B b hb zx zy hzx hzy
  refine (?_ : (ffc_offSupportLattice B).Reachable x zx).trans
    (((?_ : (ffc_offSupportLattice B).Reachable zx zy).trans
      (?_ : (ffc_offSupportLattice B).Reachable zy y)))
  · exact (ffc_reachable_iff_offSupportWalk hx).mpr ⟨px, hpx⟩
  · exact (ffc_reachable_iff_offSupportWalk
      (by have := hpx zx px.end_mem_support; exact this)).mpr ⟨pc, hpc⟩
  · exact ((ffc_reachable_iff_offSupportWalk hy).mpr ⟨py, hpy⟩).symm

/-- The L-shaped walk from `(x0, y0)` to `(x1, y1)`: vertically along column `x0` to `(x0, y1)`,
then horizontally along row `y1`. Compare `sw_lshape`, which goes horizontally first. -/
noncomputable def arcns_vlshape (x0 y0 x1 y1 : ℤ) :
    (hypercubicLattice 2).Walk ![x0, y0] ![x1, y1] :=
  (sw_vertSeg x0 y0 y1).append (sw_horizSeg y1 x0 x1)

/-- The support of `arcns_vlshape` is the union of its vertical and horizontal segments. -/
theorem arcns_vlshape_support (x0 y0 x1 y1 : ℤ) (z : Site 2) :
    z ∈ (arcns_vlshape x0 y0 x1 y1).support
      ↔ (∃ t : ℤ, t ∈ Set.uIcc y0 y1 ∧ z = ![x0, t])
        ∨ (∃ t : ℤ, t ∈ Set.uIcc x0 x1 ∧ z = ![t, y1]) := by
  unfold arcns_vlshape
  rw [Walk.mem_support_append_iff, sw_vertSeg_mem_support, sw_horizSeg_mem_support]

/-- Every site other than `u` reaches the half-plane left of `u` by a walk avoiding `u`. -/
theorem arcns_reachesFarLeft_singlePoint (u : Site 2) :
    arcns_ReachesFarLeft ({u} : Set (Site 2)) := by
  classical
  refine ⟨u 0, by intro q hq; rw [Set.mem_singleton_iff] at hq; subst hq; rfl, ?_⟩
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  set r : ℤ := if x 1 = u 1 then x 1 + 1 else x 1 with hr
  set M : ℤ := min (x 0) (u 0) - 1 with hM
  have hru : r ≠ u 1 := by rw [hr]; split_ifs with h <;> omega
  have hx0ne : x 1 = u 1 → x 0 ≠ u 0 := by
    intro h hc; exact hx (by funext i; fin_cases i <;> simp_all)
  have estart : (![x 0, x 1] : Site 2) = x := by funext i; fin_cases i <;> rfl
  refine ⟨![M, r], (arcns_vlshape (x 0) (x 1) M r).copy estart rfl, ?_, by
    simp only [Matrix.cons_val_zero]; omega⟩
  intro w hw hwu
  rw [Set.mem_singleton_iff] at hwu
  rw [Walk.support_copy, arcns_vlshape_support] at hw
  rcases hw with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · have hw0 : x 0 = u 0 := by have := congrFun hwu 0; simpa using this
    have hw1 : t = u 1 := by have := congrFun hwu 1; simpa using this
    by_cases hc : x 1 = u 1
    · exact hx0ne hc hw0
    · rw [hr, ite_eq_right hc, Set.uIcc_self, Set.mem_singleton_iff] at ht
      exact hc (by rw [← ht, hw1])
  · have hw1 : r = u 1 := by have := congrFun hwu 1; simpa using this
    exact hru hw1

/-- The square lattice with one site removed is connected. -/
theorem arcns_singlePoint_connected (u : Site 2) :
    arcns_OffSupportConnected ({u} : Set (Site 2)) :=
  arcns_connected_of_reachesFarLeft (arcns_reachesFarLeft_singlePoint u)

/-- Adding the site `u'` to `S` preserves connectivity of the complement. This is false in
general (`lrc_leafRemovable_false`): a site added next to a nearly closed ring can enclose a
site. -/
def arcns_LeafRemovable (S : Set (Site 2)) (u' : Site 2) : Prop :=
  arcns_OffSupportConnected S → arcns_OffSupportConnected (insert u' S)

/-- The support set of `cons h q` is the support set of `q` with the first site added. -/
theorem arcns_cons_support {u v w : Site 2} (h : (hypercubicLattice 2).Adj u v)
    (q : (hypercubicLattice 2).Walk v w) :
    {z : Site 2 | z ∈ (Walk.cons h q).support}
      = insert u {z : Site 2 | z ∈ q.support} := by
  ext z
  simp only [Walk.support_cons, List.mem_cons, Set.mem_ofPred_eq, Set.mem_insert_iff]

/-- An instance of `arcns_singlePoint_connected`: off the origin, `(1, 0)` reaches `(0, 1)`. -/
theorem arcns_singlePoint_nonvacuous :
    (ffc_offSupportLattice ({![0, 0]} : Set (Site 2))).Reachable ![1, 0] ![0, 1] := by
  apply arcns_singlePoint_connected
  · simp only [Set.mem_singleton_iff]; intro h; have := congrFun h 0; simp at this
  · simp only [Set.mem_singleton_iff]; intro h; have := congrFun h 1; simp at this

/-- Adding one site to the empty set keeps the complement connected. -/
theorem arcns_leafRemovable_empty (u : Site 2) :
    arcns_LeafRemovable (∅ : Set (Site 2)) u := by
  intro _
  have hins : (insert u (∅ : Set (Site 2))) = ({u} : Set (Site 2)) := by simp
  rw [hins]; exact arcns_singlePoint_connected u

end Lattice

end StatMech
