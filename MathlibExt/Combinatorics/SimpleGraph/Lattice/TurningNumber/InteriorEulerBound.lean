/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.WalkCellBoundary
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.AngleDefect
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.CellEulerCharacteristic
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.CycleRank
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanClusterBridge
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanEnclosure
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.PlanarFaceGeometric
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellEuler
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.DirectionWalk
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.InteriorCells
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.WalkCellRegion
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.WhitneyBridge
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellEulerBound

/-!
# The Euler characteristic of the interior of a simple closed walk

The 1-skeleton of a finite cell set `S` is a planar subgraph of `ℤ²`. Each cell of `S` is a bounded
face of it, and the number of bounded faces is at most the cycle rank (nullity) `E - V + c`. When
the skeleton is connected this gives `|S| ≤ E - V + 1`, that is `eulerChar S ≤ 1`. The skeleton of
the interior of a simple closed walk without right turns is connected, so its Euler characteristic
is at most `1`.

## Main definitions

* `StatMech.Onsager.CellEulerFaithful.cellSkeleton`: the 1-skeleton of `S` as a simple graph.
* `StatMech.Onsager.CellEulerFaithful.cellSkeletonP`: the same as a planar subgraph of `ℤ²`.
* `StatMech.Onsager.CellEulerFaithful.occupiedBoundedFace`: the bounded face formed by a cell.

## Main results

* `StatMech.Onsager.CellEulerFaithful.card_le_cellSkeleton_nullity`: `|S|` is at most the nullity.
* `StatMech.Onsager.CellEulerFaithful.eulerChar_le_one_of_skeleton_connected`.
* `StatMech.Onsager.CellEulerFaithful.eulerChar_interiorCells_le_one`.
-/

@[expose] public section

namespace StatMech.Onsager.CellEulerFaithful

open Finset SimpleGraph Set
open StatMech.Lattice StatMech.CellEulerChar StatMech.AngleDefect
open StatMech.Onsager.CellCount StatMech.Onsager.CellEuler
  StatMech.Onsager.CellEulerBound StatMech.Onsager.WalkCellRegion
  StatMech.Onsager.WalkCellBoundary StatMech.Onsager.BaseCase

/-- The 1-skeleton of the cell complex `S`: vertices are the corners of cells, edges the sides of
  cells. -/
def cellSkeleton (S : Finset Cell) : SimpleGraph {v // v ∈ regVerts S} where
  Adj a b := s(a.1, b.1) ∈ StatMech.CellEulerChar.regEdges S
  symm := ⟨fun a b h => by rwa [Sym2.eq_swap]⟩
  loopless := ⟨by
    intro a h
    exact wad_edge_not_diag h (by simp)⟩

/-- The 1-skeleton of `S` as a planar subgraph of `ℤ²`. -/
noncomputable def cellSkeletonP (S : Finset Cell) : PlanarZ2Subgraph where
  V := {v // v ∈ regVerts S}
  finV := inferInstance
  decV := inferInstance
  G := cellSkeleton S
  emb := ⟨fun v => ![v.1.1, v.1.2], by
    intro a b h
    apply Subtype.ext
    apply Prod.ext
    · exact congrFun h 0
    · exact congrFun h 1⟩
  isSub := by
    intro a b hab
    change s(a.1, b.1) ∈ StatMech.CellEulerChar.regEdges S at hab
    rw [StatMech.CellEulerChar.regEdges, Finset.mem_biUnion] at hab
    obtain ⟨c, _, he⟩ := hab
    obtain ⟨x, y⟩ := c
    simp only [StatMech.CellEulerChar.cellEdges, Finset.mem_insert, Finset.mem_singleton] at he
    rw [hypercubicLattice_adj, Fin.sum_univ_two]
    change (a.1.1 - b.1.1).natAbs + (a.1.2 - b.1.2).natAbs = 1
    rcases he with he | he | he | he <;> rw [Sym2.eq_iff] at he <;>
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp only [Prod.ext_iff] at h1 h2 <;> omega

/-- An edge of the cell complex is an edge of the embedded skeleton. -/
theorem regEdge_mem_imageGraph (S : Finset Cell) {e : Sym2 Vtx}
    (he : e ∈ StatMech.CellEulerChar.regEdges S) :
    Sym2.map (fun v : Vtx => ![v.1, v.2]) e ∈ (imageGraph (cellSkeletonP S)).edgeSet := by
  induction e with
  | h a b =>
      have ha : a ∈ regVerts S := wad_edge_mem_regVerts he (by simp)
      have hb : b ∈ regVerts S := wad_edge_mem_regVerts he (by simp)
      simp only [Sym2.map_mk]
      rw [SimpleGraph.mem_edgeSet, imageGraph_adj]
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, he, rfl, rfl⟩

/-- The side shared by a cell of `S` and an adjacent face is an edge of `S`. -/
theorem sharedPrimalEdge_mem_regEdges (S : Finset Cell) (c : Cell) (hc : c ∈ S)
    (g : Site 2) (hlat : (hypercubicLattice 2).Adj (cellFace c) g) :
    Sym2.map cellFace.symm (sharedPrimalEdge (cellFace c) g) ∈
      StatMech.CellEulerChar.regEdges S := by
  obtain ⟨x, y⟩ := c
  have hdist := hlat
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hdist
  simp only [cellFace_zero, cellFace_one] at hdist
  have hcases : g = ![x + 1, y] ∨ g = ![x - 1, y] ∨
      g = ![x, y + 1] ∨ g = ![x, y - 1] := by
    by_cases hx : g 0 = x
    · have hy : g 1 = y + 1 ∨ g 1 = y - 1 := by
        have : (y - g 1).natAbs = 1 := by omega
        rcases Int.natAbs_eq_iff.mp this with h | h <;> omega
      rcases hy with hy | hy
      · right; right; left
        funext i; fin_cases i <;> simp [hx, hy]
      · right; right; right
        funext i; fin_cases i <;> simp [hx, hy]
    · have hy : g 1 = y := by omega
      have hx' : g 0 = x + 1 ∨ g 0 = x - 1 := by
        have : (x - g 0).natAbs = 1 := by omega
        rcases Int.natAbs_eq_iff.mp this with h | h <;> omega
      rcases hx' with hx' | hx'
      · left; funext i; fin_cases i <;> simp [hx', hy]
      · right; left; funext i; fin_cases i <;> simp [hx', hy]
  rw [StatMech.CellEulerChar.regEdges, Finset.mem_biUnion]
  refine ⟨(x, y), hc, ?_⟩
  rcases hcases with rfl | rfl | rfl | rfl
  · change Sym2.map cellFace.symm (sharedPrimalEdge ![x, y] ![x + 1, y]) ∈ _
    rw [sharedPrimalEdge_right]
    simp [Sym2.map_mk, StatMech.CellEulerChar.cellEdges, faceCorner10, faceCorner11]
  · change Sym2.map cellFace.symm (sharedPrimalEdge ![x, y] ![x - 1, y]) ∈ _
    rw [sharedPrimalEdge_left]
    simp [Sym2.map_mk, StatMech.CellEulerChar.cellEdges, faceCorner00, faceCorner01]
  · change Sym2.map cellFace.symm (sharedPrimalEdge ![x, y] ![x, y + 1]) ∈ _
    rw [sharedPrimalEdge_top]
    simp [Sym2.map_mk, StatMech.CellEulerChar.cellEdges, faceCorner01, faceCorner11]
  · change Sym2.map cellFace.symm (sharedPrimalEdge ![x, y] ![x, y - 1]) ∈ _
    rw [sharedPrimalEdge_bottom]
    simp [Sym2.map_mk, StatMech.CellEulerChar.cellEdges, faceCorner00, faceCorner10]

/-- The face of a cell of `S` is enclosed by the skeleton on all four sides. -/
theorem occupiedFace_isolated (S : Finset Cell) (c : Cell) (hc : c ∈ S) (g : Site 2) :
    ¬ (whb_faceRegion (imageGraph (cellSkeletonP S))).Adj (cellFace c) g := by
  intro hadj
  rw [whb_faceRegion_adj] at hadj
  apply hadj.2
  have he := sharedPrimalEdge_mem_regEdges S c hc g hadj.1
  have himg := regEdge_mem_imageGraph S he
  generalize hedge : sharedPrimalEdge (cellFace c) g = e at he himg ⊢
  induction e with
  | h a b =>
      simp only [Sym2.map_mk] at himg ⊢
      convert himg using 1
      rw [Sym2.eq_iff]
      left
      constructor <;> funext i <;> fin_cases i <;> rfl

/-- The face component of the skeleton containing the cell `c`. -/
noncomputable def occupiedComponent (S : Finset Cell) (c : Cell) :
    (whb_faceRegion (imageGraph (cellSkeletonP S))).ConnectedComponent :=
  (whb_faceRegion (imageGraph (cellSkeletonP S))).connectedComponentMk (cellFace c)

/-- The face of a cell of `S` is alone in its face component. -/
theorem occupiedFace_reachable_eq (S : Finset Cell) (c : Cell) (hc : c ∈ S) (g : Site 2)
    (hreach : (whb_faceRegion (imageGraph (cellSkeletonP S))).Reachable (cellFace c) g) :
    g = cellFace c := by
  obtain ⟨p⟩ := hreach
  cases p with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (occupiedFace_isolated S c hc _)

/-- The face component of a cell of `S` is bounded. -/
theorem occupiedComponent_finite (S : Finset Cell) (c : Cell) (hc : c ∈ S) :
    (occupiedComponent S c).supp.Finite := by
  apply Set.Finite.subset (Set.finite_singleton (cellFace c))
  intro g hg
  have hbase : cellFace c ∈ (occupiedComponent S c).supp := by
    rw [ConnectedComponent.mem_supp_iff]
    rfl
  have hreach := (occupiedComponent S c).reachable_of_mem_supp hbase hg
  exact occupiedFace_reachable_eq S c hc g hreach

/-- The bounded face of the skeleton formed by a cell of `S`. -/
noncomputable def occupiedBoundedFace (S : Finset Cell) (c : S) :
    jcb_BoundedRegion (cellSkeletonP S) :=
  ⟨occupiedComponent S c.1, occupiedComponent_finite S c.1 c.2⟩

/-- Distinct cells form distinct bounded faces. -/
theorem occupiedBoundedFace_injective (S : Finset Cell) :
    Function.Injective (occupiedBoundedFace S) := by
  intro c d h
  have hcomp : occupiedComponent S c.1 = occupiedComponent S d.1 := congrArg Subtype.val h
  have hreach : (whb_faceRegion (imageGraph (cellSkeletonP S))).Reachable
      (cellFace c.1) (cellFace d.1) := ConnectedComponent.eq.mp hcomp
  have hface : cellFace d.1 = cellFace c.1 :=
    occupiedFace_reachable_eq S c.1 c.2 (cellFace d.1) hreach
  exact Subtype.ext (cellFace.injective hface.symm)

/-- The number of cells is at most the nullity of the skeleton. -/
theorem card_le_cellSkeleton_nullity (S : Finset Cell) :
    S.card ≤ nullity (cellSkeletonP S).G := by
  have hle := Nat.card_le_card_of_injective (occupiedBoundedFace S)
    (occupiedBoundedFace_injective S)
  rw [Nat.card_eq_fintype_card, Fintype.card_coe,
    jcb_boundedRegion_card_eq_nullity] at hle
  exact hle

theorem mem_cellSkeleton_edgeSet_iff (S : Finset Cell)
    (e : Sym2 {v // v ∈ regVerts S}) :
    e ∈ (cellSkeleton S).edgeSet ↔
      Sym2.map Subtype.val e ∈ StatMech.CellEulerChar.regEdges S := by
  induction e with
  | h a b => rfl

/-- The edges of `cellSkeleton S` are the edges of the cell complex `S`. -/
noncomputable def cellSkeletonEdgeEquiv (S : Finset Cell) :
    {e // e ∈ (cellSkeleton S).edgeSet} ≃ {e // e ∈ StatMech.CellEulerChar.regEdges S} where
  toFun e := ⟨Sym2.map Subtype.val e.1, by
    exact (mem_cellSkeleton_edgeSet_iff S e.1).mp e.2⟩
  invFun e := ⟨e.1.attachWith (fun v hv => wad_edge_mem_regVerts e.2 hv), by
    rw [mem_cellSkeleton_edgeSet_iff]
    simpa only [Sym2.attachWith_map_subtypeVal] using e.2⟩
  left_inv e := by
    apply Subtype.ext
    apply Sym2.map.injective Subtype.val_injective
    simp only [Sym2.attachWith_map_subtypeVal]
  right_inv e := by
    apply Subtype.ext
    simp only [Sym2.attachWith_map_subtypeVal]

theorem card_cellSkeleton_edges (S : Finset Cell) :
    Nat.card (cellSkeleton S).edgeSet = (StatMech.CellEulerChar.regEdges S).card := by
  rw [Nat.card_congr (cellSkeletonEdgeEquiv S), Nat.card_eq_fintype_card, Fintype.card_coe]

/-- The skeleton has `(regVerts S).card` vertices. -/
theorem card_cellSkeleton_vertices (S : Finset Cell) :
    Nat.card {v // v ∈ regVerts S} = (regVerts S).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]

/-- If the 1-skeleton of `S` is connected, then `eulerChar S ≤ 1`. See also
  `StatMech.Onsager.CellEulerBound.eulerChar_le_one`. -/
theorem eulerChar_le_one_of_skeleton_connected (S : Finset Cell)
    (hconn : (cellSkeleton S).Connected) : eulerChar S ≤ 1 := by
  have hnull := card_le_cellSkeleton_nullity S
  have hcomp : Nat.card (cellSkeleton S).ConnectedComponent = 1 :=
    card_components_eq_one_of_connected hconn
  have hvertices := card_cellSkeleton_vertices S
  have hedges := card_cellSkeleton_edges S
  have hedges' : (cellSkeleton S).edgeSet.ncard =
      (StatMech.CellEulerChar.regEdges S).card := by
    rw [← Nat.card_coe_set_eq, hedges]
  have htree := hconn.card_vert_le_card_edgeSet_add_one
  rw [hvertices, hedges] at htree
  change S.card ≤ nullity (cellSkeleton S) at hnull
  unfold nullity at hnull
  rw [hcomp, hvertices, hedges'] at hnull
  rw [eulerChar_eq_regChi]
  unfold regChi
  omega

/-- A corner of a cell of `S`, as a vertex of the skeleton. -/
def skeletonVertexOfCorner (S : Finset Cell) (c : Cell) (hc : c ∈ S)
    (v : Vtx) (hv : v ∈ StatMech.CellEulerChar.cellVerts c) : {v // v ∈ regVerts S} :=
  ⟨v, wad_cellVerts_subset_regVerts hc hv⟩

/-- Every corner of a cell is connected in the skeleton to its lower-left corner. -/
theorem corner_reachable_lowerLeft (S : Finset Cell) (c : Cell) (hc : c ∈ S)
    (v : Vtx) (hv : v ∈ StatMech.CellEulerChar.cellVerts c) :
    (cellSkeleton S).Reachable (skeletonVertexOfCorner S c hc v hv)
      (skeletonVertexOfCorner S c hc c (by
        obtain ⟨x, y⟩ := c
        simp [StatMech.CellEulerChar.cellVerts])) := by
  obtain ⟨x, y⟩ := c
  have hedge (a b : Vtx) (he : s(a, b) ∈ StatMech.CellEulerChar.cellEdges (x, y)) :
      (cellSkeleton S).Adj
        (skeletonVertexOfCorner S (x, y) hc a (by
          have ha := wad_edge_mem_regVerts (K := {(x, y)}) (by
            simpa [StatMech.CellEulerChar.regEdges] using he) (show a ∈ s(a, b) by simp)
          simpa [regVerts] using ha))
        (skeletonVertexOfCorner S (x, y) hc b (by
          have hb := wad_edge_mem_regVerts (K := {(x, y)}) (by
            simpa [StatMech.CellEulerChar.regEdges] using he) (show b ∈ s(a, b) by simp)
          simpa [regVerts] using hb)) := by
    change s(a, b) ∈ StatMech.CellEulerChar.regEdges S
    rw [StatMech.CellEulerChar.regEdges, Finset.mem_biUnion]
    exact ⟨(x, y), hc, he⟩
  have hbottom := hedge (x, y) (x + 1, y) (by simp [StatMech.CellEulerChar.cellEdges])
  have hleft := hedge (x, y) (x, y + 1) (by simp [StatMech.CellEulerChar.cellEdges])
  have hright := hedge (x + 1, y) (x + 1, y + 1) (by simp [StatMech.CellEulerChar.cellEdges])
  simp only [StatMech.CellEulerChar.cellVerts, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with hv | hv | hv | hv
  · subst v; exact Reachable.refl _
  · subst v; exact hbottom.reachable.symm
  · subst v; exact hleft.reachable.symm
  · subst v; exact hright.reachable.symm.trans hbottom.reachable.symm

/-- The lower-left corners of two adjacent cells of `S` are connected in the skeleton. -/
theorem cell_representatives_reachable_of_adj (S : Finset Cell) (c d : Cell)
    (hc : c ∈ S) (hd : d ∈ S)
    (hadj : (hypercubicLattice 2).Adj (cellFace c) (cellFace d)) :
    (cellSkeleton S).Reachable
      (skeletonVertexOfCorner S c hc c (by
        obtain ⟨x, y⟩ := c; simp [StatMech.CellEulerChar.cellVerts]))
      (skeletonVertexOfCorner S d hd d (by
        obtain ⟨x, y⟩ := d; simp [StatMech.CellEulerChar.cellVerts])) := by
  let e := Sym2.map cellFace.symm (sharedPrimalEdge (cellFace c) (cellFace d))
  have hec : e ∈ StatMech.CellEulerChar.regEdges ({c} : Finset Cell) :=
    sharedPrimalEdge_mem_regEdges {c} c (by simp) (cellFace d) hadj
  have hed : e ∈ StatMech.CellEulerChar.regEdges ({d} : Finset Cell) := by
    have h := sharedPrimalEdge_mem_regEdges {d} d (by simp) (cellFace c) hadj.symm
    rw [← sharedPrimalEdge_comm_of_adj hadj] at h
    exact h
  generalize heq : e = edge at hec hed
  induction edge with
  | h a b =>
      have hac : a ∈ StatMech.CellEulerChar.cellVerts c := by
        have h := wad_edge_mem_regVerts (K := {c}) hec (show a ∈ s(a, b) by simp)
        simpa [regVerts] using h
      have had : a ∈ StatMech.CellEulerChar.cellVerts d := by
        have h := wad_edge_mem_regVerts (K := {d}) hed (show a ∈ s(a, b) by simp)
        simpa [regVerts] using h
      have hca := (corner_reachable_lowerLeft S c hc a hac).symm
      have hda := corner_reachable_lowerLeft S d hd a had
      exact hca.trans hda

/-- The lower-left corner of a cell of `S`, as a vertex of the skeleton. -/
def skeletonRepresentative (S : Finset Cell) (c : S) : {v // v ∈ regVerts S} :=
  skeletonVertexOfCorner S c.1 c.2 c.1 (by
    obtain ⟨x, y⟩ := c.1
    simp [StatMech.CellEulerChar.cellVerts])

/-- Any two interior cells of a simple closed walk without right turns have skeleton-connected
  lower-left corners. -/
theorem interior_representatives_reachable {m : ℕ}
    (d : Fin (m + 3) → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (BaseCase.pos d))
    (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
    (c e : interiorCells d hclosed hsimple hreflexfree) :
    (cellSkeleton (interiorCells d hclosed hsimple hreflexfree)).Reachable
      (skeletonRepresentative _ c) (skeletonRepresentative _ e) := by
  let S := interiorCells d hclosed hsimple hreflexfree
  let R := walkRegionGraph d hclosed hsimple
  let C := innerComponent d hclosed hsimple hreflexfree
  have hcSupp : cellFace c.1 ∈ C.supp := by
    simpa [S, C] using (mem_interiorCells d hclosed hsimple hreflexfree c.1).mp c.2
  have heSupp : cellFace e.1 ∈ C.supp := by
    simpa [S, C] using (mem_interiorCells d hclosed hsimple hreflexfree e.1).mp e.2
  have hreach : R.Reachable (cellFace c.1) (cellFace e.1) :=
    C.reachable_of_mem_supp hcSupp heSupp
  obtain ⟨p⟩ := hreach
  have cellMem : ∀ (f : Site 2), f ∈ C.supp → cellFace.symm f ∈ S := by
    intro f hf
    rw [mem_interiorCells]
    rw [cellFace.apply_symm_apply]
    exact hf
  have lift : ∀ {f g : Site 2} (q : R.Walk f g) (hf : f ∈ C.supp) (hg : g ∈ C.supp),
      (cellSkeleton S).Reachable
        (skeletonRepresentative S ⟨cellFace.symm f, cellMem f hf⟩)
        (skeletonRepresentative S ⟨cellFace.symm g, cellMem g hg⟩) := by
    intro f g q
    induction q with
    | nil => intro _ _; exact Reachable.refl _
    | @cons a b z hab q ih =>
        intro ha hz
        have hb : b ∈ C.supp := C.mem_supp_of_adj_mem_supp ha hab
        have hlat : (hypercubicLattice 2).Adj
            (cellFace (cellFace.symm a)) (cellFace (cellFace.symm b)) := by
          simpa using hab.1
        have hstep := cell_representatives_reachable_of_adj S
          (cellFace.symm a) (cellFace.symm b) (cellMem a ha) (cellMem b hb) hlat
        have hstep' : (cellSkeleton S).Reachable
            (skeletonRepresentative S ⟨cellFace.symm a, cellMem a ha⟩)
            (skeletonRepresentative S ⟨cellFace.symm b, cellMem b hb⟩) := by
          simpa [skeletonRepresentative] using hstep
        exact hstep'.trans (ih hb hz)
  have h := lift p hcSupp heSupp
  simpa [S, skeletonRepresentative] using h

/-- The skeleton of the interior of a simple closed walk without right turns is connected. -/
theorem interior_cellSkeleton_connected {m : ℕ}
    (d : Fin (m + 3) → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    (cellSkeleton (interiorCells d hclosed hsimple hreflexfree)).Connected := by
  let S := interiorCells d hclosed hsimple hreflexfree
  rw [connected_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨u, hu⟩ ⟨v, hv⟩
    rw [regVerts, Finset.mem_biUnion] at hu hv
    obtain ⟨c, hc, huc⟩ := hu
    obtain ⟨e, he, hve⟩ := hv
    have hucRep : (cellSkeleton S).Reachable ⟨u, hu⟩
        (skeletonRepresentative S ⟨c, hc⟩) := by
      simpa [S, skeletonRepresentative, skeletonVertexOfCorner] using
        corner_reachable_lowerLeft S c hc u huc
    have hce := interior_representatives_reachable d hclosed hsimple hreflexfree
      (⟨c, hc⟩ : S) (⟨e, he⟩ : S)
    have hevRep : (cellSkeleton S).Reachable ⟨v, hv⟩
        (skeletonRepresentative S ⟨e, he⟩) := by
      simpa [S, skeletonRepresentative, skeletonVertexOfCorner] using
        corner_reachable_lowerLeft S e he v hve
    exact hucRep.trans (hce.trans hevRep.symm)
  · let k : Fin (m + 3) := 0
    have hc : leftCell d k ∈ S :=
      leftCell_mem_interiorCells d hclosed hsimple hreflexfree k
    exact ⟨skeletonRepresentative S ⟨leftCell d k, hc⟩⟩

/-- The interior of a simple closed walk without right turns has Euler characteristic at most
  `1`. -/
theorem eulerChar_interiorCells_le_one {m : ℕ}
    (d : Fin (m + 3) → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    eulerChar (interiorCells d hclosed hsimple hreflexfree) ≤ 1 :=
  eulerChar_le_one_of_skeleton_connected _
    (interior_cellSkeleton_connected d hclosed hsimple hreflexfree)

end StatMech.Onsager.CellEulerFaithful
