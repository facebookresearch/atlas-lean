/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.AngleDefect
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellEuler

/-!
# An Euler characteristic bound for cell sets

This file identifies the Euler characteristic `StatMech.Onsager.CellEuler.eulerChar` with the
Euler characteristic `StatMech.CellEulerChar.regChi` of the cell complex of
`MathlibExt.Combinatorics.SimpleGraph.Lattice.CellEulerCharacteristic`, and proves
`eulerChar S ≤ 1` when the skeleton of `S` with the top edge of every cell removed is connected:
the top edges are in bijection with the cells, and a connected graph has at least `V - 1` edges.

## Main definitions

* `StatMech.Onsager.CellEulerBound.edgeCode`: the doubled-midpoint code of a lattice edge.
* `StatMech.Onsager.CellEulerBound.topEdge`, `StatMech.Onsager.CellEulerBound.topEdges`: the top
  edges of the cells.
* `StatMech.Onsager.CellEulerBound.openTopSkeleton`: the skeleton without top edges.

## Main results

* `StatMech.Onsager.CellEulerBound.eulerChar_eq_regChi`.
* `StatMech.Onsager.CellEulerBound.eulerChar_le_one`.
-/

@[expose] public section

namespace StatMech.Onsager.CellEulerBound

open Finset SimpleGraph
open StatMech.CellEulerChar StatMech.AngleDefect
open StatMech.Onsager.CellCount StatMech.Onsager.CellEuler

/-- The lattice edge `{a, b}` encoded by the sum `a + b`, twice its midpoint; injective on unit
  edges. -/
def edgeCode : Sym2 (ℤ × ℤ) → ℤ × ℤ :=
  Sym2.lift ⟨fun a b => (a.1 + b.1, a.2 + b.2), by
    intro a b
    ext <;> simp only <;> omega⟩

@[simp] theorem edgeCode_mk (a b : ℤ × ℤ) :
    edgeCode s(a, b) = (a.1 + b.1, a.2 + b.2) := rfl

/-- The codes of the edges of a cell are `StatMech.Onsager.CellEuler.edgesOf`. -/
theorem image_cellEdges_edgeCode (c : Cell) :
    (StatMech.CellEulerChar.cellEdges c).image edgeCode = edgesOf c := by
  obtain ⟨x, y⟩ := c
  ext e
  simp only [StatMech.CellEulerChar.cellEdges, edgesOf, mem_image, mem_insert, mem_singleton]
  constructor
  · rintro ⟨z, (rfl | rfl | rfl | rfl), rfl⟩ <;> simp <;> omega
  · rintro (rfl | rfl | rfl | rfl)
    · refine ⟨s(((x, y)), ((x + 1, y))), by simp, ?_⟩
      simp only [edgeCode_mk, Prod.mk.injEq]
      constructor <;> omega
    · refine ⟨s(((x, y + 1)), ((x + 1, y + 1))), by simp, ?_⟩
      simp only [edgeCode_mk, Prod.mk.injEq]
      omega
    · refine ⟨s(((x, y)), ((x, y + 1))), by simp, ?_⟩
      simp only [edgeCode_mk, Prod.mk.injEq]
      omega
    · refine ⟨s(((x + 1, y)), ((x + 1, y + 1))), by simp, ?_⟩
      simp only [edgeCode_mk, Prod.mk.injEq]
      omega

theorem image_regEdges_edgeCode (S : Finset Cell) :
    (regEdges S).image edgeCode = StatMech.Onsager.CellEuler.cellEdges S := by
  ext e
  rw [mem_image, StatMech.Onsager.CellEuler.cellEdges, mem_biUnion]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [regEdges, mem_biUnion] at hz
    obtain ⟨c, hc, hzc⟩ := hz
    refine ⟨c, hc, ?_⟩
    have hz : edgeCode z ∈ (StatMech.CellEulerChar.cellEdges c).image edgeCode :=
      mem_image.mpr ⟨z, hzc, rfl⟩
    rwa [image_cellEdges_edgeCode] at hz
  · rintro ⟨c, hc, hec⟩
    have he : e ∈ (StatMech.CellEulerChar.cellEdges c).image edgeCode := by
      rwa [image_cellEdges_edgeCode]
    obtain ⟨z, hzc, rfl⟩ := mem_image.mp he
    refine ⟨z, ?_, rfl⟩
    rw [regEdges, mem_biUnion]
    exact ⟨c, hc, hzc⟩

theorem edgeCode_injOn_regEdges (S : Finset Cell) :
    Set.InjOn edgeCode (regEdges S) := by
  intro e he f hf hef
  have he' : e ∈ regEdges S := he
  have hf' : f ∈ regEdges S := hf
  simp only [regEdges, mem_biUnion] at he' hf'
  obtain ⟨c, -, hec⟩ := he'
  obtain ⟨d, -, hfd⟩ := hf'
  obtain ⟨x, y⟩ := c
  obtain ⟨u, v⟩ := d
  simp only [StatMech.CellEulerChar.cellEdges, mem_insert, mem_singleton] at hec hfd
  rcases hec with rfl | rfl | rfl | rfl <;>
    rcases hfd with rfl | rfl | rfl | rfl <;>
    simp only [edgeCode_mk, Prod.mk.injEq] at hef <;>
    rw [Sym2.eq_iff] <;>
    simp only [Prod.mk.injEq] <;>
    omega

/-- The two edge counts of a cell complex agree. -/
theorem card_cellEdges_eq_regEdges (S : Finset Cell) :
    (StatMech.Onsager.CellEuler.cellEdges S).card = (regEdges S).card := by
  rw [← image_regEdges_edgeCode S, card_image_iff.mpr]
  intro e he f hf h
  exact edgeCode_injOn_regEdges S he hf h

/-- The two vertex sets of a cell complex agree. -/
theorem cellVerts_eq_regVerts (S : Finset Cell) :
    StatMech.Onsager.CellCount.cellVerts S = regVerts S := by
  ext v
  simp only [StatMech.Onsager.CellCount.cellVerts, regVerts, mem_biUnion]
  constructor
  · rintro ⟨c, hc, hv⟩
    refine ⟨c, hc, ?_⟩
    obtain ⟨x, y⟩ := c
    simp only [cornersOf, StatMech.CellEulerChar.cellVerts, mem_insert, mem_singleton] at hv ⊢
    omega
  · rintro ⟨c, hc, hv⟩
    refine ⟨c, hc, ?_⟩
    obtain ⟨x, y⟩ := c
    simp only [cornersOf, StatMech.CellEulerChar.cellVerts, mem_insert, mem_singleton] at hv ⊢
    omega

/-- The Euler characteristic `eulerChar` agrees with `StatMech.CellEulerChar.regChi`. -/
theorem eulerChar_eq_regChi (S : Finset Cell) : eulerChar S = regChi S := by
  unfold eulerChar regChi
  rw [cellVerts_eq_regVerts, card_cellEdges_eq_regEdges]

/-- The top edge of the cell `c`. -/
def topEdge (c : Cell) : Sym2 Vtx :=
  s((c.1, c.2 + 1), (c.1 + 1, c.2 + 1))

/-- The top edges of the cells of `S`. -/
def topEdges (S : Finset Cell) : Finset (Sym2 Vtx) := S.image topEdge

theorem topEdge_injective : Function.Injective topEdge := by
  rintro ⟨x, y⟩ ⟨u, v⟩ h
  simp only [topEdge, Sym2.eq_iff, Prod.mk.injEq] at h
  rcases h with h | h <;> simp_all; omega

/-- Distinct cells have distinct top edges. -/
theorem card_topEdges (S : Finset Cell) : (topEdges S).card = S.card := by
  exact card_image_of_injective S topEdge_injective

theorem topEdges_subset_regEdges (S : Finset Cell) : topEdges S ⊆ regEdges S := by
  intro e he
  obtain ⟨c, hc, rfl⟩ := mem_image.mp he
  exact mem_biUnion.mpr ⟨c, hc, by simp [topEdge, StatMech.CellEulerChar.cellEdges]⟩

/-- The 1-skeleton of the cell complex `S` with the top edge of every cell removed, as a simple
  graph on its vertices. -/
def openTopSkeleton (S : Finset Cell) : SimpleGraph {v // v ∈ regVerts S} where
  Adj a b := s(a.1, b.1) ∈ regEdges S \ topEdges S
  symm := ⟨fun a b h => by
    rwa [Sym2.eq_swap]⟩
  loopless := ⟨by
    intro a h
    exact (wad_edge_not_diag (mem_sdiff.mp h).1) (by simp)⟩

theorem mem_openTopSkeleton_edgeSet_iff (S : Finset Cell)
    (e : Sym2 {v // v ∈ regVerts S}) :
    e ∈ (openTopSkeleton S).edgeSet ↔
      Sym2.map Subtype.val e ∈ regEdges S \ topEdges S := by
  induction e with
  | h a b => rfl

/-- The edges of `openTopSkeleton S` are the edges of `S` other than top edges. -/
noncomputable def openTopEdgeEquiv (S : Finset Cell) :
    {e // e ∈ (openTopSkeleton S).edgeSet} ≃ {e // e ∈ regEdges S \ topEdges S} where
  toFun e := ⟨Sym2.map Subtype.val e.1,
    (mem_openTopSkeleton_edgeSet_iff S e.1).mp e.2⟩
  invFun e := ⟨e.1.attachWith (fun v hv =>
      wad_edge_mem_regVerts (mem_sdiff.mp e.2).1 hv), by
    rw [mem_openTopSkeleton_edgeSet_iff]
    simpa only [Sym2.attachWith_map_subtypeVal] using e.2⟩
  left_inv e := by
    apply Subtype.ext
    apply Sym2.map.injective Subtype.val_injective
    simp only [Sym2.attachWith_map_subtypeVal]
  right_inv e := by
    apply Subtype.ext
    simp only [Sym2.attachWith_map_subtypeVal]

theorem card_openTopSkeleton_edges (S : Finset Cell) :
    Nat.card (openTopSkeleton S).edgeSet = (regEdges S \ topEdges S).card := by
  rw [Nat.card_congr (openTopEdgeEquiv S), Nat.card_eq_fintype_card, Fintype.card_coe]

/-- If the open-top skeleton is connected, it has at least as many edges as vertices minus one. -/
theorem regVerts_card_le (S : Finset Cell) (hconn : (openTopSkeleton S).Connected) :
    (regVerts S).card ≤ (regEdges S \ topEdges S).card + 1 := by
  have h := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_openTopSkeleton_edges] at h
  exact h

/-- If the open-top skeleton of `S` is connected, then `regChi S ≤ 1`. -/
theorem regChi_le_one (S : Finset Cell) (hconn : (openTopSkeleton S).Connected) :
    regChi S ≤ 1 := by
  have hv := regVerts_card_le S hconn
  have hsplit := card_sdiff_add_card (regEdges S) (topEdges S)
  rw [union_eq_left.mpr (topEdges_subset_regEdges S), card_topEdges] at hsplit
  unfold regChi
  omega

/-- If the open-top skeleton of `S` is connected, then `eulerChar S ≤ 1`. See also
  `StatMech.Onsager.CellEulerFaithful.eulerChar_le_one_of_skeleton_connected`, which assumes
  connectivity of the full skeleton. -/
theorem eulerChar_le_one (S : Finset Cell) (hconn : (openTopSkeleton S).Connected) :
    eulerChar S ≤ 1 := by
  rw [eulerChar_eq_regChi]
  exact regChi_le_one S hconn

end StatMech.Onsager.CellEulerBound
