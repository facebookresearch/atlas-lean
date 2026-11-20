/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.CellEuler
import Code.Walls.wadangledefect

namespace StatMech.Onsager.CellEulerBound

open Finset SimpleGraph
open StatMech.Euc StatMech.Wad
open StatMech.Onsager.CellCount StatMech.Onsager.CellEuler


def edgeCode : Sym2 (ℤ × ℤ) → ℤ × ℤ :=
  Sym2.lift ⟨fun a b => (a.1 + b.1, a.2 + b.2), by
    intro a b
    ext <;> simp only <;> omega⟩

@[simp] theorem edgeCode_mk (a b : ℤ × ℤ) :
    edgeCode s(a, b) = (a.1 + b.1, a.2 + b.2) := rfl



theorem image_cellEdges_edgeCode (c : Cell) :
    (StatMech.Euc.cellEdges c).image edgeCode = edgesOf c := by
  obtain ⟨x, y⟩ := c
  ext e
  simp only [StatMech.Euc.cellEdges, edgesOf, mem_image, mem_insert, mem_singleton,
    edgeCode_mk, Prod.mk.injEq]
  constructor
  · rintro ⟨z, (rfl | rfl | rfl | rfl), rfl⟩ <;> simp <;> omega
  · rintro (rfl | rfl | rfl | rfl)
    · refine ⟨s(((x, y)), ((x + 1, y))), by simp, ?_⟩
      simp only [edgeCode_mk, Prod.mk.injEq]
      constructor <;> omega
    · refine ⟨s(((x, y + 1)), ((x + 1, y + 1))), by simp, ?_⟩
      simp only [edgeCode_mk, Prod.mk.injEq]
      congr 1 <;> omega
    · refine ⟨s(((x, y)), ((x, y + 1))), by simp, ?_⟩
      simp only [edgeCode_mk, Prod.mk.injEq]
      congr 1 <;> omega
    · refine ⟨s(((x + 1, y)), ((x + 1, y + 1))), by simp, ?_⟩
      simp only [edgeCode_mk, Prod.mk.injEq]
      congr 1 <;> omega


theorem image_regEdges_edgeCode (S : Finset Cell) :
    (regEdges S).image edgeCode = StatMech.Onsager.CellEuler.cellEdges S := by
  ext e
  rw [mem_image, StatMech.Onsager.CellEuler.cellEdges, mem_biUnion]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [regEdges, mem_biUnion] at hz
    obtain ⟨c, hc, hzc⟩ := hz
    refine ⟨c, hc, ?_⟩
    have hz : edgeCode z ∈ (StatMech.Euc.cellEdges c).image edgeCode :=
      mem_image.mpr ⟨z, hzc, rfl⟩
    rwa [image_cellEdges_edgeCode] at hz
  · rintro ⟨c, hc, hec⟩
    have he : e ∈ (StatMech.Euc.cellEdges c).image edgeCode := by
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
  simp only [StatMech.Euc.cellEdges, mem_insert, mem_singleton] at hec hfd
  rcases hec with rfl | rfl | rfl | rfl <;>
    rcases hfd with rfl | rfl | rfl | rfl <;>
    simp only [edgeCode_mk, Prod.mk.injEq] at hef <;>
    rw [Sym2.eq_iff] <;>
    simp only [Prod.mk.injEq] <;>
    omega


theorem card_cellEdges_eq_regEdges (S : Finset Cell) :
    (StatMech.Onsager.CellEuler.cellEdges S).card = (regEdges S).card := by
  rw [← image_regEdges_edgeCode S, card_image_iff.mpr]
  intro e he f hf h
  exact edgeCode_injOn_regEdges S he hf h


theorem cellVerts_eq_regVerts (S : Finset Cell) :
    StatMech.Onsager.CellCount.cellVerts S = regVerts S := by
  ext v
  simp only [StatMech.Onsager.CellCount.cellVerts, regVerts, mem_biUnion]
  constructor
  · rintro ⟨c, hc, hv⟩
    refine ⟨c, hc, ?_⟩
    obtain ⟨x, y⟩ := c
    simp only [cornersOf, StatMech.Euc.cellVerts, mem_insert, mem_singleton,
      Prod.mk.injEq] at hv ⊢
    omega
  · rintro ⟨c, hc, hv⟩
    refine ⟨c, hc, ?_⟩
    obtain ⟨x, y⟩ := c
    simp only [cornersOf, StatMech.Euc.cellVerts, mem_insert, mem_singleton,
      Prod.mk.injEq] at hv ⊢
    omega


theorem eulerChar_eq_regChi (S : Finset Cell) : eulerChar S = regChi S := by
  unfold eulerChar regChi
  rw [cellVerts_eq_regVerts, card_cellEdges_eq_regEdges]


def topEdge (c : Cell) : Sym2 Vtx :=
  s((c.1, c.2 + 1), (c.1 + 1, c.2 + 1))


def topEdges (S : Finset Cell) : Finset (Sym2 Vtx) := S.image topEdge

theorem topEdge_injective : Function.Injective topEdge := by
  rintro ⟨x, y⟩ ⟨u, v⟩ h
  simp only [topEdge, Sym2.eq_iff, Prod.mk.injEq] at h
  rcases h with h | h <;> simp_all <;> omega

theorem card_topEdges (S : Finset Cell) : (topEdges S).card = S.card := by
  exact card_image_of_injective S topEdge_injective

theorem topEdges_subset_regEdges (S : Finset Cell) : topEdges S ⊆ regEdges S := by
  intro e he
  obtain ⟨c, hc, rfl⟩ := mem_image.mp he
  exact mem_biUnion.mpr ⟨c, hc, by simp [topEdge, StatMech.Euc.cellEdges]⟩


def openTopSkeleton (S : Finset Cell) : SimpleGraph {v // v ∈ regVerts S} where
  Adj a b := s(a.1, b.1) ∈ regEdges S \ topEdges S
  symm := by
    intro a b h
    rwa [Sym2.eq_swap]
  loopless := ⟨by
    intro a h
    exact (wad_edge_not_diag (mem_sdiff.mp h).1) (by simp)⟩

theorem mem_openTopSkeleton_edgeSet_iff (S : Finset Cell)
    (e : Sym2 {v // v ∈ regVerts S}) :
    e ∈ (openTopSkeleton S).edgeSet ↔
      Sym2.map Subtype.val e ∈ regEdges S \ topEdges S := by
  induction e with
  | h a b => rfl



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


theorem regVerts_card_le (S : Finset Cell) (hconn : (openTopSkeleton S).Connected) :
    (regVerts S).card ≤ (regEdges S \ topEdges S).card + 1 := by
  have h := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_openTopSkeleton_edges] at h
  exact h




theorem regChi_le_one (S : Finset Cell) (hconn : (openTopSkeleton S).Connected) :
    regChi S ≤ 1 := by
  have hv := regVerts_card_le S hconn
  have hsplit := card_sdiff_add_card (regEdges S) (topEdges S)
  rw [union_eq_left.mpr (topEdges_subset_regEdges S), card_topEdges] at hsplit
  unfold regChi
  push_cast
  omega

theorem eulerChar_le_one (S : Finset Cell) (hconn : (openTopSkeleton S).Connected) :
    eulerChar S ≤ 1 := by
  rw [eulerChar_eq_regChi]
  exact regChi_le_one S hconn

end StatMech.Onsager.CellEulerBound
