/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.InterfaceConnected
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.SegmentDownCounterexample

/-!
# King-move connectivity of the off-support interior

The king graph `mci_kingGraph` on `Site 2 = Fin 2 → ℤ` joins distinct sites that differ by at most
one in each coordinate; it contains the square lattice (`mci_hyper_le_king`). For a closed walk
`Vc`, `mci_KingInteriorConnected Vc` says that some off-support interior site is joined to every
off-support interior site by a king walk through the off-support interior. It follows from the
square-lattice predicate `jil_RowLinked` and from connectivity of the induced king graph
`mci_interiorKingGraph Vc`.

`mci_FourThin Vc` says that every lattice edge between two sites of `Vc` is an edge of `Vc`. For a
simple closed walk this is Rosenfeld's notion of a simple closed 4-curve, for which the interior
is 8-connected (king-move connected). The fjord walk `sdc_fjord` is not 4-thin
(`mci_fjord_not_fourThin`).

## Main definitions

* `StatMech.Lattice.mci_kingAdj`, `StatMech.Lattice.mci_kingGraph`: king adjacency and the king
  graph on `ℤ²`. See also `KingAdj` and `boundaryKingGraph`.
* `StatMech.Lattice.mci_FourThin Vc`: lattice edges between support sites are edges of `Vc`.
* `StatMech.Lattice.mci_interiorKingGraph Vc`: the king graph induced on the off-support interior.
* `StatMech.Lattice.mci_KingRowLinked Vc seed`: every off-support interior site reaches `seed` by
  a king walk through the off-support interior.
* `StatMech.Lattice.mci_KingInteriorConnected Vc`: some off-support interior site is a king
  row-linked seed.

## Main results

* `StatMech.Lattice.mci_hyper_le_king`: the square lattice is a subgraph of the king graph.
* `StatMech.Lattice.mci_kingAdj_iff_kingAdj`, `StatMech.Lattice.mci_boundaryKingGraph_eq_induce`:
  the bridges to `KingAdj` and `boundaryKingGraph`.
* `StatMech.Lattice.mci_offSupport_walk_interior`: a lattice walk avoiding `Vc` that starts in the
  off-support interior stays there.
* `StatMech.Lattice.mci_fjord_not_fourThin`: the fjord walk is not 4-thin.
* `StatMech.Lattice.mci_kingInteriorConnected_of_rowLinked`,
  `StatMech.Lattice.mci_kingInteriorConnected_of_kingStepConn`: sufficient conditions for king
  connectivity of the off-support interior.

## References

* A. Rosenfeld, *Arcs and curves in digital pictures*, J. ACM 20 (1973), 81–87.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- King adjacency on `ℤ²`: `u ≠ v` and the coordinates differ by at most one. The same relation as
`KingAdj` (`mci_kingAdj_iff_kingAdj`). -/
def mci_kingAdj (u v : Site 2) : Prop :=
  (u 0 - v 0).natAbs ≤ 1 ∧ (u 1 - v 1).natAbs ≤ 1 ∧ u ≠ v

theorem mci_kingAdj_symm : ∀ ⦃u v : Site 2⦄, mci_kingAdj u v → mci_kingAdj v u := by
  rintro u v ⟨h0, h1, hne⟩
  refine ⟨?_, ?_, hne.symm⟩
  · rw [← Int.natAbs_neg, neg_sub]; exact h0
  · rw [← Int.natAbs_neg, neg_sub]; exact h1

theorem mci_kingAdj_irrefl : ∀ u, ¬ mci_kingAdj u u := by
  rintro u ⟨_, _, hne⟩; exact hne rfl

/-- The king graph on `ℤ²`: each site is adjacent to its eight neighbours. -/
def mci_kingGraph : SimpleGraph (Site 2) where
  Adj := mci_kingAdj
  symm := ⟨fun _ _ h => mci_kingAdj_symm h⟩
  loopless := ⟨mci_kingAdj_irrefl⟩

@[simp] theorem mci_kingGraph_adj (u v : Site 2) :
    mci_kingGraph.Adj u v ↔
      (u 0 - v 0).natAbs ≤ 1 ∧ (u 1 - v 1).natAbs ≤ 1 ∧ u ≠ v := Iff.rfl

/-- `mci_kingAdj` agrees with `KingAdj`, which states the same relation with the coordinates
quantified. -/
theorem mci_kingAdj_iff_kingAdj (u v : Site 2) : mci_kingAdj u v ↔ KingAdj u v := by
  constructor
  · rintro ⟨h0, h1, hne⟩
    exact ⟨hne, Fin.forall_fin_two.mpr ⟨h0, h1⟩⟩
  · rintro ⟨hne, h⟩
    exact ⟨h 0, h 1, hne⟩

/-- The king graph on the complement of `K` is the king graph `mci_kingGraph` induced on `Kᶜ`. -/
theorem mci_boundaryKingGraph_eq_induce (K : Set (Site 2)) :
    boundaryKingGraph K = mci_kingGraph.induce Kᶜ := by
  ext a b
  exact (mci_kingAdj_iff_kingAdj _ _).symm

/-- The square lattice is a subgraph of the king graph. -/
theorem mci_hyper_le_king : hypercubicLattice 2 ≤ mci_kingGraph := by
  intro u v hadj
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  refine ⟨by omega, by omega, ?_⟩
  intro h; rw [h] at hadj; simp at hadj

/-- Lattice reachability implies king reachability. -/
theorem mci_kingReachable_of_hyperReachable {u v : Site 2}
    (h : (hypercubicLattice 2).Reachable u v) : mci_kingGraph.Reachable u v :=
  h.mono mci_hyper_le_king

/-- Diagonal neighbours are king-adjacent. -/
theorem mci_kingAdj_diag (x y : ℤ) (sx sy : ℤ) (hsx : sx = 1 ∨ sx = -1)
    (hsy : sy = 1 ∨ sy = -1) :
    mci_kingGraph.Adj (![x, y] : Site 2) ![x + sx, y + sy] := by
  refine ⟨by simp; omega, by simp; omega, ?_⟩
  intro h
  have := congrFun h 0
  simp only [Matrix.cons_val_zero] at this; omega

/-- Both ends of an edge of the vertical segment `jec_vsegUp col r k` lie in column `col`. -/
theorem mci_vseg_edge_col (col r : ℤ) (k : ℕ) {u v : Site 2}
    (he : s(u, v) ∈ (jec_vsegUp col r k).edges) : u 0 = col ∧ v 0 = col :=
  ⟨(jec_vsegUp_support col r k ((jec_vsegUp col r k).fst_mem_support_of_mem_edges he)).1,
   (jec_vsegUp_support col r k ((jec_vsegUp col r k).snd_mem_support_of_mem_edges he)).1⟩

/-- Both ends of an edge of the horizontal segment `jec_hsegRight row t k` lie in row `row`. -/
theorem mci_hseg_edge_row (row t : ℤ) (k : ℕ) {u v : Site 2}
    (he : s(u, v) ∈ (jec_hsegRight row t k).edges) : u 1 = row ∧ v 1 = row :=
  ⟨(jec_hsegRight_support row t k ((jec_hsegRight row t k).fst_mem_support_of_mem_edges he)).1,
   (jec_hsegRight_support row t k ((jec_hsegRight row t k).snd_mem_support_of_mem_edges he)).1⟩

/-- The closed walk `Vc` is 4-thin: every lattice edge between two of its sites is an edge of `Vc`.
For a simple closed walk this means each site of `Vc` has exactly two lattice neighbours on `Vc`. -/
def mci_FourThin {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  ∀ u v : Site 2, u ∈ Vc.support → v ∈ Vc.support →
    (hypercubicLattice 2).Adj u v → s(u, v) ∈ Vc.edges

/-- The lattice edge from `(3, 1)` to `(4, 1)` is not an edge of the fjord walk. -/
theorem mci_fjord_no_row1_horizontal_edge :
    s((![3, 1] : Site 2), (![4, 1] : Site 2)) ∉ sdc_fjord.edges := by
  intro hedge
  unfold sdc_fjord at hedge
  simp only [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_copy,
    SimpleGraph.Walk.edges_reverse, List.mem_append, List.mem_reverse] at hedge
  rcases hedge with h|h|h|h|h|h|h|h
  · have := (mci_hseg_edge_row 0 0 3 h).1; simp at this
  · have := (mci_vseg_edge_col 3 0 3 h).2; simp at this
  · have := (mci_hseg_edge_row 3 3 1 h).1; simp at this
  · have := (mci_vseg_edge_col 4 0 3 h).1; simp at this
  · have := (mci_hseg_edge_row 0 4 3 h).1; simp at this
  · have := (mci_vseg_edge_col 7 0 4 h).1; simp at this
  · have := (mci_hseg_edge_row 4 0 7 h).1; simp at this
  · have := (mci_vseg_edge_col 0 0 4 h).1; simp at this

/-- The site `(3, 1)` is on the fjord walk. -/
theorem mci_fjord_on_31 : (![3, 1] : Site 2) ∈ sdc_fjord.support := by
  unfold sdc_fjord
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; left
  exact sdc_vsegUp_mem' 3 0 3 1 (by norm_num) (by norm_num)

/-- The fjord walk `sdc_fjord` is not 4-thin: `(3, 1)` and `(4, 1)` are lattice neighbours on the
walk not joined by an edge of the walk. -/
theorem mci_fjord_not_fourThin : ¬ mci_FourThin sdc_fjord := by
  intro hthin
  have hadj : (hypercubicLattice 2).Adj (![3, 1] : Site 2) ![4, 1] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide
  exact mci_fjord_no_row1_horizontal_edge (hthin _ _ mci_fjord_on_31 sdc_fjord_on_41 hadj)

/-- The sites `(2, 1)` and `(5, 1)`, in the two rooms of the fjord walk, are not king-adjacent. -/
theorem mci_fjord_pockets_not_king_adjacent :
    ¬ mci_kingGraph.Adj (![2, 1] : Site 2) (![5, 1] : Site 2) := by
  rw [mci_kingGraph_adj]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, not_and]
  intro h; omega

/-- The king graph induced on the off-support interior of `Vc`. -/
def mci_interiorKingGraph {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    SimpleGraph (jil_offSupportInterior Vc) :=
  mci_kingGraph.induce (jil_offSupportInterior Vc)

/-- Lattice neighbours in the off-support interior are adjacent in `mci_interiorKingGraph`. -/
theorem mci_interiorKingGraph_axial_adj {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : jil_offSupportInterior Vc}
    (hadj : (hypercubicLattice 2).Adj (u : Site 2) (v : Site 2)) :
    (mci_interiorKingGraph Vc).Adj u v := by
  rw [mci_interiorKingGraph, SimpleGraph.induce_adj]
  exact mci_hyper_le_king hadj

/-- King neighbours in the off-support interior are adjacent in `mci_interiorKingGraph`. -/
theorem mci_interiorKingGraph_adj {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : jil_offSupportInterior Vc}
    (hadj : mci_kingGraph.Adj (u : Site 2) (v : Site 2)) :
    (mci_interiorKingGraph Vc).Adj u v := by
  rw [mci_interiorKingGraph, SimpleGraph.induce_adj]
  exact hadj

/-- The induced square lattice on the off-support interior is a subgraph of the induced king graph.
-/
theorem mci_interiorStepGraph_le_king {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    jil_interiorStepGraph Vc ≤ mci_interiorKingGraph Vc := by
  intro u v hadj
  rw [jil_interiorStepGraph, SimpleGraph.induce_adj] at hadj
  exact mci_interiorKingGraph_axial_adj Vc hadj

/-- A lattice neighbour off `Vc` of an off-support interior site is in the off-support interior. -/
theorem mci_offSupport_neighbor_interior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z w : Site 2} (hz : z ∈ jil_offSupportInterior Vc)
    (hadj : (hypercubicLattice 2).Adj z w) (hwoff : w ∉ Vc.support) :
    w ∈ jil_offSupportInterior Vc := by
  obtain ⟨hzoff, hzint⟩ := (jil_mem_offSupportInterior Vc _).mp hz
  have hpar := jec_localConstancy Vc hadj hzoff hwoff
  rw [jil_mem_offSupportInterior]
  refine ⟨hwoff, ?_⟩
  rw [jec_mem_leftRegion] at hzint ⊢
  intro h; exact hzint (hpar.mpr h)

/-- A lattice walk avoiding `Vc` that starts in the off-support interior stays in it. See also
`jlri_sameRegion_along_offSupport_walk`, the same fact for the endpoints and the inside. -/
theorem mci_offSupport_walk_interior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (p : (hypercubicLattice 2).Walk x y)
    (hp : ∀ z ∈ p.support, z ∉ Vc.support)
    (hx : x ∈ jil_offSupportInterior Vc) :
    ∀ z ∈ p.support, z ∈ jil_offSupportInterior Vc := by
  induction p with
  | nil =>
    intro z hz
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz; exact hz ▸ hx
  | @cons u v w hadj q ih =>
    have hv : v ∉ Vc.support := hp v (by simp [SimpleGraph.Walk.support_cons])
    have htail : ∀ z ∈ q.support, z ∉ Vc.support := fun z hz =>
      hp z (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hz)
    have hvint : v ∈ jil_offSupportInterior Vc :=
      mci_offSupport_neighbor_interior Vc hx hadj hv
    have ihv := ih htail hvint
    intro z hz
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with h | h
    · exact h ▸ hx
    · exact ihv z h

/-- Two diagonal off-support interior sites `(x, y)` and `(x + 1, y + 1)` are joined through `(x +
1, y)` in the induced king graph when `(x + 1, y)` is off `Vc`. -/
theorem mci_diagonal_king_bridge {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {x y : ℤ}
    (hxy : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hdiag : (![x + 1, y + 1] : Site 2) ∈ jil_offSupportInterior Vc)
    (helb_off : (![x + 1, y] : Site 2) ∉ Vc.support) :
    ∃ helb : (![x + 1, y] : Site 2) ∈ jil_offSupportInterior Vc,
      (mci_interiorKingGraph Vc).Adj ⟨![x, y], hxy⟩ ⟨![x + 1, y], helb⟩ ∧
      (mci_interiorKingGraph Vc).Adj ⟨![x + 1, y], helb⟩ ⟨![x + 1, y + 1], hdiag⟩ := by
  have hadj_left : (hypercubicLattice 2).Adj (![x, y] : Site 2) ![x + 1, y] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  have helb : (![x + 1, y] : Site 2) ∈ jil_offSupportInterior Vc :=
    mci_offSupport_neighbor_interior Vc hxy hadj_left helb_off
  refine ⟨helb, ?_, ?_⟩
  · exact mci_interiorKingGraph_axial_adj Vc (u := ⟨_, hxy⟩) (v := ⟨_, helb⟩) hadj_left
  · have hadj_up : (hypercubicLattice 2).Adj (![x + 1, y] : Site 2) ![x + 1, y + 1] := by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
    exact mci_interiorKingGraph_axial_adj Vc (u := ⟨_, helb⟩) (v := ⟨_, hdiag⟩) hadj_up

/-- Two diagonal off-support interior sites are reachable from each other in the induced king graph
when the corner `(x + 1, y)` is off `Vc`. -/
theorem mci_diagonal_king_reachable {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {x y : ℤ}
    (hxy : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hdiag : (![x + 1, y + 1] : Site 2) ∈ jil_offSupportInterior Vc)
    (helb_off : (![x + 1, y] : Site 2) ∉ Vc.support) :
    (mci_interiorKingGraph Vc).Reachable ⟨![x, y], hxy⟩ ⟨![x + 1, y + 1], hdiag⟩ := by
  obtain ⟨_helb, h1, h2⟩ := mci_diagonal_king_bridge Vc hxy hdiag helb_off
  exact (h1.reachable).trans h2.reachable

/-- A walk in the induced king graph is a king walk through the off-support interior. -/
theorem mci_kingStepGraph_walk_interior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : jil_offSupportInterior Vc}
    (w : (mci_interiorKingGraph Vc).Walk x y) :
    ∃ p : mci_kingGraph.Walk (x : Site 2) (y : Site 2),
      ∀ z ∈ p.support, z ∈ jil_offSupportInterior Vc := by
  classical
  induction w with
  | @nil u => exact ⟨SimpleGraph.Walk.nil, by
      intro z hz
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      subst hz; exact u.2⟩
  | @cons u v t hadj q ih =>
    obtain ⟨p, hp⟩ := ih
    have hadj' : mci_kingGraph.Adj (u : Site 2) (v : Site 2) := by
      rw [mci_interiorKingGraph] at hadj
      exact SimpleGraph.induce_adj.mp hadj
    refine ⟨SimpleGraph.Walk.cons hadj' p, ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with h | h
    · subst h; exact u.2
    · exact hp z h

/-- Every off-support interior site of `Vc` is joined to `seed` by a king walk through the
off-support interior. -/
def mci_KingRowLinked {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (seed : Site 2) : Prop :=
  ∀ z ∈ jil_offSupportInterior Vc,
    ∃ p : mci_kingGraph.Walk z seed, ∀ w ∈ p.support, w ∈ jil_offSupportInterior Vc

/-- Reachability in the induced king graph gives a king row-linked seed. -/
theorem mci_kingRowLinked_of_kingStepReachable {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseedI : seed ∈ jil_offSupportInterior Vc)
    (hstep : ∀ z : jil_offSupportInterior Vc,
      (mci_interiorKingGraph Vc).Reachable z ⟨seed, hseedI⟩) :
    mci_KingRowLinked Vc seed := by
  intro z hz
  obtain ⟨w⟩ := hstep ⟨z, hz⟩
  exact mci_kingStepGraph_walk_interior Vc w

/-- A row-linked seed is king row-linked. -/
theorem mci_kingRowLinked_of_rowLinked {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hlink : jil_RowLinked Vc seed) :
    mci_KingRowLinked Vc seed := by
  intro z hz
  obtain ⟨p, hp⟩ := hlink z hz
  refine ⟨p.mapLe mci_hyper_le_king, ?_⟩
  intro w hw
  rw [SimpleGraph.Walk.support_mapLe_eq_support mci_hyper_le_king p] at hw
  exact mci_offSupport_walk_interior Vc p hp hz w hw

/-- The off-support interior of `Vc` is king-move connected around some seed: some off-support
interior site is king row-linked. For a nonempty off-support interior this is connectivity of
`mci_interiorKingGraph Vc`. -/
def mci_KingInteriorConnected {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  ∃ seed, seed ∈ jil_offSupportInterior Vc ∧ mci_KingRowLinked Vc seed

/-- Connectivity of the induced king graph to an off-support interior seed gives king connectivity
of the off-support interior. -/
theorem mci_kingInteriorConnected_of_kingStepConn {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) {seed : Site 2}
    (hseedI : seed ∈ jil_offSupportInterior Vc)
    (hstep : ∀ z : jil_offSupportInterior Vc,
      (mci_interiorKingGraph Vc).Reachable z ⟨seed, hseedI⟩) :
    mci_KingInteriorConnected Vc :=
  ⟨seed, hseedI, mci_kingRowLinked_of_kingStepReachable Vc hseedI hstep⟩

/-- A row-linked off-support interior seed gives king connectivity of the off-support interior. -/
theorem mci_kingInteriorConnected_of_rowLinked {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) {seed : Site 2}
    (hseedI : seed ∈ jil_offSupportInterior Vc) (hlink : jil_RowLinked Vc seed) :
    mci_KingInteriorConnected Vc :=
  ⟨seed, hseedI, mci_kingRowLinked_of_rowLinked Vc hlink⟩

end Lattice

end StatMech
