/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Mathlib
import Code.Walls.euceuler

open scoped BigOperators
open Finset
open StatMech.Euc

namespace StatMech.Wad




def surroundCells (v : Vtx) : Finset Cell :=
  {(v.1 - 1, v.2 - 1), (v.1, v.2 - 1), (v.1 - 1, v.2), (v.1, v.2)}



def cellDeg (K : Finset Cell) (v : Vtx) : ℕ := (surroundCells v ∩ K).card



def edgeDeg (K : Finset Cell) (v : Vtx) : ℕ :=
  ((regEdges K).filter (fun e => v ∈ e)).card






theorem wad_mem_surround_iff (v : Vtx) (c : Cell) :
    c ∈ surroundCells v ↔ v ∈ cellVerts c := by
  obtain ⟨x, y⟩ := v; obtain ⟨a, b⟩ := c
  unfold surroundCells cellVerts
  simp only [mem_insert, mem_singleton, Prod.mk.injEq]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega


theorem wad_cellVerts_subset_regVerts {K : Finset Cell} {c : Cell} (hc : c ∈ K) :
    cellVerts c ⊆ regVerts K := by
  intro v hv; unfold regVerts; exact mem_biUnion.mpr ⟨c, hc, hv⟩



theorem wad_cellVerts_inter_regVerts {K : Finset Cell} {c : Cell} (hc : c ∈ K) :
    cellVerts c ∩ regVerts K = cellVerts c :=
  inter_eq_left.mpr (wad_cellVerts_subset_regVerts hc)











theorem wad_angleSum (K : Finset Cell) :
    ∑ v ∈ regVerts K, cellDeg K v = 4 * K.card := by
  classical
  have hcell : ∀ v ∈ regVerts K,
      cellDeg K v = ∑ c ∈ K, (if c ∈ surroundCells v then 1 else 0) := by
    intro v _
    unfold cellDeg
    rw [inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
  rw [Finset.sum_congr rfl hcell, Finset.sum_comm]
  
  have hinner : ∀ c ∈ K,
      (∑ v ∈ regVerts K, if c ∈ surroundCells v then 1 else 0) = 4 := by
    intro c hc
    have : (∑ v ∈ regVerts K, if c ∈ surroundCells v then 1 else 0)
        = ((regVerts K).filter (fun v => c ∈ surroundCells v)).card := by
      rw [Finset.card_filter]
    rw [this]
    have hset : (regVerts K).filter (fun v => c ∈ surroundCells v) = cellVerts c := by
      ext v
      rw [mem_filter, wad_mem_surround_iff]
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h; exact ⟨wad_cellVerts_subset_regVerts hc h, h⟩
    rw [hset, euc_cellVerts_card]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
  ring





theorem wad_edge_not_diag {K : Finset Cell} {e : Sym2 Vtx} (he : e ∈ regEdges K) :
    ¬ e.IsDiag := by
  unfold regEdges at he
  rw [mem_biUnion] at he
  obtain ⟨c, _, hce⟩ := he
  obtain ⟨a, b⟩ := c
  unfold cellEdges at hce
  simp only [mem_insert, mem_singleton] at hce
  rcases hce with h | h | h | h <;>
    (subst h; rw [Sym2.mk_isDiag_iff]; simp only [Prod.mk.injEq, not_and]; omega)


theorem wad_edge_mem_regVerts {K : Finset Cell} {e : Sym2 Vtx} (he : e ∈ regEdges K)
    {v : Vtx} (hv : v ∈ e) : v ∈ regVerts K := by
  unfold regEdges at he
  rw [mem_biUnion] at he
  obtain ⟨c, hc, hce⟩ := he
  apply wad_cellVerts_subset_regVerts hc
  obtain ⟨a, b⟩ := c
  unfold cellEdges at hce
  unfold cellVerts
  simp only [mem_insert, mem_singleton] at hce ⊢
  rcases hce with h | h | h | h <;>
    (subst h; rw [Sym2.mem_iff] at hv; obtain ⟨x, y⟩ := v;
     rcases hv with h | h <;> (rw [Prod.ext_iff] at h; simp only [Prod.mk.injEq]; omega))



theorem wad_endpoints_card {K : Finset Cell} {e : Sym2 Vtx} (he : e ∈ regEdges K) :
    ((regVerts K).filter (fun v => v ∈ e)).card = 2 := by
  classical
  induction e with
  | h a b =>
    have hne : a ≠ b := by
      have h := wad_edge_not_diag he
      rw [Sym2.mk_isDiag_iff] at h; exact h
    have hset : (regVerts K).filter (fun v => v ∈ (s(a, b) : Sym2 Vtx)) = {a, b} := by
      ext v
      simp only [mem_filter, Sym2.mem_iff, mem_insert, mem_singleton]
      constructor
      · rintro ⟨_, h | h⟩ <;> [left; right] <;> exact h
      · rintro (h | h)
        · exact ⟨wad_edge_mem_regVerts he (h ▸ Sym2.mem_mk_left a b), Or.inl h⟩
        · exact ⟨wad_edge_mem_regVerts he (h ▸ Sym2.mem_mk_right a b), Or.inr h⟩
    rw [hset, card_insert_of_notMem (by simp [hne]), card_singleton]








theorem wad_edgeSum (K : Finset Cell) :
    ∑ v ∈ regVerts K, edgeDeg K v = 2 * (regEdges K).card := by
  classical
  have hedge : ∀ v ∈ regVerts K,
      edgeDeg K v = ∑ e ∈ regEdges K, (if v ∈ e then 1 else 0) := by
    intro v _; unfold edgeDeg; rw [Finset.card_filter]
  rw [Finset.sum_congr rfl hedge, Finset.sum_comm]
  have hinner : ∀ e ∈ regEdges K,
      (∑ v ∈ regVerts K, if v ∈ e then 1 else 0) = 2 := by
    intro e he
    rw [← Finset.card_filter]; exact wad_endpoints_card he
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
  ring








def defect (K : Finset Cell) (v : Vtx) : ℤ :=
  4 - 2 * (edgeDeg K v : ℤ) + (cellDeg K v : ℤ)










theorem wad_defect_eq_four_chi (K : Finset Cell) :
    ∑ v ∈ regVerts K, defect K v = 4 * regChi K := by
  classical
  have hexpand : ∑ v ∈ regVerts K, defect K v
      = 4 * ((regVerts K).card : ℤ)
        - 2 * (∑ v ∈ regVerts K, (edgeDeg K v : ℤ))
        + (∑ v ∈ regVerts K, (cellDeg K v : ℤ)) := by
    unfold defect
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum]
    ring
  rw [hexpand]
  have hA : (∑ v ∈ regVerts K, (cellDeg K v : ℤ)) = 4 * (K.card : ℤ) := by
    rw [← Nat.cast_sum, wad_angleSum]; push_cast; ring
  have hB : (∑ v ∈ regVerts K, (edgeDeg K v : ℤ)) = 2 * ((regEdges K).card : ℤ) := by
    rw [← Nat.cast_sum, wad_edgeSum]; push_cast; ring
  rw [hA, hB]
  unfold regChi
  ring









def incidentEdgeR (v : Vtx) : Sym2 Vtx := s(v, (v.1 + 1, v.2))
def incidentEdgeL (v : Vtx) : Sym2 Vtx := s(v, (v.1 - 1, v.2))
def incidentEdgeU (v : Vtx) : Sym2 Vtx := s(v, (v.1, v.2 + 1))
def incidentEdgeD (v : Vtx) : Sym2 Vtx := s(v, (v.1, v.2 - 1))




theorem wad_edge_incident_cases {K : Finset Cell} {e : Sym2 Vtx} (he : e ∈ regEdges K)
    {v : Vtx} (hv : v ∈ e) :
    e = incidentEdgeR v ∨ e = incidentEdgeL v ∨ e = incidentEdgeU v ∨ e = incidentEdgeD v := by
  unfold regEdges at he
  rw [mem_biUnion] at he
  obtain ⟨c, _, hce⟩ := he
  obtain ⟨a, b⟩ := c; obtain ⟨x, y⟩ := v
  unfold cellEdges at hce
  simp only [mem_insert, mem_singleton] at hce
  simp only [incidentEdgeR, incidentEdgeL, incidentEdgeU, incidentEdgeD, Sym2.eq_iff,
    Prod.mk.injEq]
  rcases hce with h | h | h | h <;> subst h <;>
    simp only [Sym2.mem_iff, Prod.mk.injEq] at hv <;>
    obtain (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) := hv <;> simp




theorem wad_incidentR_mem (K : Finset Cell) (v : Vtx) :
    incidentEdgeR v ∈ regEdges K ↔ (v ∈ K ∨ (v.1, v.2 - 1) ∈ K) := by
  obtain ⟨x, y⟩ := v
  unfold regEdges incidentEdgeR
  rw [mem_biUnion]
  constructor
  · rintro ⟨c, hc, hce⟩; obtain ⟨a, b⟩ := c
    unfold cellEdges at hce
    simp only [mem_insert, mem_singleton, Sym2.eq_iff, Prod.mk.injEq] at hce
    
    have hcell : ((a : ℤ) = x ∧ b = y) ∨ ((a : ℤ) = x ∧ b = y - 1) := by
      rcases hce with h | h | h | h <;> omega
    rcases hcell with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hc
    · exact Or.inr (by simpa using hc)
  · rintro (h | h)
    · refine ⟨(x, y), h, ?_⟩; unfold cellEdges
      simp [Sym2.eq_iff]
    · refine ⟨(x, y - 1), h, ?_⟩; unfold cellEdges
      simp [Sym2.eq_iff]


theorem wad_incidentL_mem (K : Finset Cell) (v : Vtx) :
    incidentEdgeL v ∈ regEdges K ↔ ((v.1 - 1, v.2) ∈ K ∨ (v.1 - 1, v.2 - 1) ∈ K) := by
  obtain ⟨x, y⟩ := v
  unfold regEdges incidentEdgeL
  rw [mem_biUnion]
  constructor
  · rintro ⟨c, hc, hce⟩; obtain ⟨a, b⟩ := c
    unfold cellEdges at hce
    simp only [mem_insert, mem_singleton, Sym2.eq_iff, Prod.mk.injEq] at hce
    have hcell : ((a : ℤ) = x - 1 ∧ b = y) ∨ ((a : ℤ) = x - 1 ∧ b = y - 1) := by
      rcases hce with h | h | h | h <;> omega
    rcases hcell with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl (by simpa using hc)
    · exact Or.inr (by simpa using hc)
  · rintro (h | h)
    · refine ⟨(x - 1, y), h, ?_⟩; unfold cellEdges
      simp [Sym2.eq_iff]
    · refine ⟨(x - 1, y - 1), h, ?_⟩; unfold cellEdges
      simp [Sym2.eq_iff]


theorem wad_incidentU_mem (K : Finset Cell) (v : Vtx) :
    incidentEdgeU v ∈ regEdges K ↔ ((v.1 - 1, v.2) ∈ K ∨ v ∈ K) := by
  obtain ⟨x, y⟩ := v
  unfold regEdges incidentEdgeU
  rw [mem_biUnion]
  constructor
  · rintro ⟨c, hc, hce⟩; obtain ⟨a, b⟩ := c
    unfold cellEdges at hce
    simp only [mem_insert, mem_singleton, Sym2.eq_iff, Prod.mk.injEq] at hce
    have hcell : ((a : ℤ) = x - 1 ∧ b = y) ∨ ((a : ℤ) = x ∧ b = y) := by
      rcases hce with h | h | h | h <;> omega
    rcases hcell with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl (by simpa using hc)
    · exact Or.inr hc
  · rintro (h | h)
    · refine ⟨(x - 1, y), h, ?_⟩; unfold cellEdges
      simp [Sym2.eq_iff]
    · refine ⟨(x, y), h, ?_⟩; unfold cellEdges
      simp [Sym2.eq_iff]


theorem wad_incidentD_mem (K : Finset Cell) (v : Vtx) :
    incidentEdgeD v ∈ regEdges K ↔ ((v.1 - 1, v.2 - 1) ∈ K ∨ (v.1, v.2 - 1) ∈ K) := by
  obtain ⟨x, y⟩ := v
  unfold regEdges incidentEdgeD
  rw [mem_biUnion]
  constructor
  · rintro ⟨c, hc, hce⟩; obtain ⟨a, b⟩ := c
    unfold cellEdges at hce
    simp only [mem_insert, mem_singleton, Sym2.eq_iff, Prod.mk.injEq] at hce
    have hcell : ((a : ℤ) = x - 1 ∧ b = y - 1) ∨ ((a : ℤ) = x ∧ b = y - 1) := by
      rcases hce with h | h | h | h <;> omega
    rcases hcell with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl (by simpa using hc)
    · exact Or.inr (by simpa using hc)
  · rintro (h | h)
    · refine ⟨(x - 1, y - 1), h, ?_⟩; unfold cellEdges
      simp [Sym2.eq_iff]
    · refine ⟨(x, y - 1), h, ?_⟩; unfold cellEdges
      simp [Sym2.eq_iff]


theorem wad_v_mem_incident (v : Vtx) :
    v ∈ incidentEdgeR v ∧ v ∈ incidentEdgeL v ∧ v ∈ incidentEdgeU v ∧ v ∈ incidentEdgeD v := by
  simp only [incidentEdgeR, incidentEdgeL, incidentEdgeU, incidentEdgeD]
  exact ⟨Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩







theorem wad_edgeDeg_eq (K : Finset Cell) (v : Vtx) :
    edgeDeg K v =
      (({incidentEdgeR v, incidentEdgeL v, incidentEdgeU v, incidentEdgeD v} : Finset (Sym2 Vtx)).filter
        (fun e => e ∈ regEdges K)).card := by
  classical
  unfold edgeDeg
  congr 1
  ext e
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · rintro ⟨he, hv⟩
    exact ⟨wad_edge_incident_cases he hv, he⟩
  · rintro ⟨hcase, he⟩
    refine ⟨he, ?_⟩
    obtain ⟨mR, mL, mU, mD⟩ := wad_v_mem_incident v
    rcases hcase with h | h | h | h <;> (subst h; assumption)













theorem wad_defect_classify (K : Finset Cell) (v : Vtx) (hv : v ∈ regVerts K) :
    defect K v = 1 ∨ defect K v = 0 ∨ defect K v = -1 ∨ defect K v = -2 := by
  classical
  
  have hcellpos : 1 ≤ cellDeg K v := by
    unfold cellDeg
    rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
    unfold regVerts at hv
    rw [mem_biUnion] at hv
    obtain ⟨c, hc, hvc⟩ := hv
    exact ⟨c, mem_inter.mpr ⟨(wad_mem_surround_iff v c).mpr hvc, hc⟩⟩
  obtain ⟨x, y⟩ := v
  
  have hcell : (cellDeg K (x, y) : ℤ) =
      (if ((x - 1, y - 1) ∈ K) then 1 else 0) + (if ((x, y - 1) ∈ K) then 1 else 0)
        + (if ((x - 1, y) ∈ K) then 1 else 0) + (if ((x, y) ∈ K) then 1 else 0) := by
    unfold cellDeg surroundCells
    dsimp only
    rw [← Finset.filter_mem_eq_inter, Finset.card_filter]
    have e1 : ((x:ℤ) - 1, y - 1) ∉ ({((x:ℤ), y - 1), (x - 1, y), (x, y)} : Finset Cell) := by
      simp only [mem_insert, mem_singleton, Prod.mk.injEq]; omega
    have e2 : ((x:ℤ), y - 1) ∉ ({((x:ℤ) - 1, y), (x, y)} : Finset Cell) := by
      simp only [mem_insert, mem_singleton, Prod.mk.injEq]; omega
    have e3 : ((x:ℤ) - 1, y) ∉ ({((x:ℤ), y)} : Finset Cell) := by
      simp only [mem_singleton, Prod.mk.injEq]; omega
    rw [Finset.sum_insert e1, Finset.sum_insert e2, Finset.sum_insert e3,
      Finset.sum_singleton]
    push_cast; ring
  
  have hedge : (edgeDeg K (x, y) : ℤ) =
      (if (((x, y) ∈ K) ∨ ((x, y - 1) ∈ K)) then 1 else 0)
        + (if (((x - 1, y) ∈ K) ∨ ((x - 1, y - 1) ∈ K)) then 1 else 0)
        + (if (((x - 1, y) ∈ K) ∨ ((x, y) ∈ K)) then 1 else 0)
        + (if (((x - 1, y - 1) ∈ K) ∨ ((x, y - 1) ∈ K)) then 1 else 0) := by
    rw [wad_edgeDeg_eq, Finset.card_filter]
    have i1 : incidentEdgeR (x, y) ∉
        ({incidentEdgeL (x, y), incidentEdgeU (x, y), incidentEdgeD (x, y)} :
          Finset (Sym2 Vtx)) := by
      simp only [incidentEdgeR, incidentEdgeL, incidentEdgeU, incidentEdgeD, mem_insert,
        mem_singleton, Sym2.eq_iff, Prod.mk.injEq]; push_neg; refine ⟨?_, ?_, ?_⟩ <;> omega
    have i2 : incidentEdgeL (x, y) ∉
        ({incidentEdgeU (x, y), incidentEdgeD (x, y)} : Finset (Sym2 Vtx)) := by
      simp only [incidentEdgeL, incidentEdgeU, incidentEdgeD, mem_insert, mem_singleton,
        Sym2.eq_iff, Prod.mk.injEq]; push_neg; refine ⟨?_, ?_⟩ <;> omega
    have i3 : incidentEdgeU (x, y) ∉ ({incidentEdgeD (x, y)} : Finset (Sym2 Vtx)) := by
      simp only [incidentEdgeD, incidentEdgeU, mem_singleton, Sym2.eq_iff, Prod.mk.injEq]
      push_neg; omega
    rw [Finset.sum_insert i1, Finset.sum_insert i2, Finset.sum_insert i3,
      Finset.sum_singleton]
    simp only [wad_incidentR_mem, wad_incidentL_mem, wad_incidentU_mem, wad_incidentD_mem]
    push_cast; ring
  
  have hcellposZ : (1 : ℤ) ≤ (cellDeg K (x, y) : ℤ) := by exact_mod_cast hcellpos
  rw [hcell] at hcellposZ
  clear hcellpos
  
  unfold defect
  rw [hcell, hedge]
  by_cases s1 : ((x - 1, y - 1) ∈ K) <;> by_cases s2 : ((x, y - 1) ∈ K) <;>
    by_cases s3 : ((x - 1, y) ∈ K) <;> by_cases s4 : ((x, y) ∈ K) <;>
    simp only [s1, s2, s3, s4, true_or, or_true, false_or, or_false,
      or_self, ↓reduceIte] at hcellposZ ⊢ <;> omega




def wad_n1 (K : Finset Cell) : ℤ :=
  ((regVerts K).filter (fun v => defect K v = 1)).card

def wad_n3 (K : Finset Cell) : ℤ :=
  ((regVerts K).filter (fun v => defect K v = -1)).card

def wad_n2d (K : Finset Cell) : ℤ :=
  ((regVerts K).filter (fun v => defect K v = -2)).card




theorem wad_defectSum_eq_counts (K : Finset Cell) :
    ∑ v ∈ regVerts K, defect K v = wad_n1 K - wad_n3 K - 2 * wad_n2d K := by
  classical
  unfold wad_n1 wad_n3 wad_n2d
  
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  rcases wad_defect_classify K v hv with h | h | h | h <;> rw [h] <;> norm_num








theorem wad_defect_eq_four_chi_counts (K : Finset Cell) :
    wad_n1 K - wad_n3 K - 2 * wad_n2d K = 4 * regChi K := by
  rw [← wad_defectSum_eq_counts, wad_defect_eq_four_chi]






theorem wad_defect_eq_four {K : Finset Cell} (hK : EucBuildable K) (hpinch : wad_n2d K = 0) :
    wad_n1 K - wad_n3 K = 4 := by
  have h := wad_defect_eq_four_chi_counts K
  rw [hpinch, euc_chi_induction hK] at h
  linarith









theorem wad_n1_unitSquare : wad_n1 ({((0:ℤ),(0:ℤ))} : Finset Cell) = 4 := by
  unfold wad_n1; decide
theorem wad_n3_unitSquare : wad_n3 ({((0:ℤ),(0:ℤ))} : Finset Cell) = 0 := by
  unfold wad_n3; decide
theorem wad_n2d_unitSquare : wad_n2d ({((0:ℤ),(0:ℤ))} : Finset Cell) = 0 := by
  unfold wad_n2d; decide

theorem wad_witness_unitSquare :
    wad_n1 ({((0:ℤ),(0:ℤ))} : Finset Cell) - wad_n3 ({((0:ℤ),(0:ℤ))} : Finset Cell) = 4 :=
  wad_defect_eq_four (EucBuildable.singleton _) wad_n2d_unitSquare


theorem wad_n2d_domino : wad_n2d ({((0:ℤ),(0:ℤ)),(1,0)} : Finset Cell) = 0 := by
  unfold wad_n2d; decide

theorem wad_witness_domino :
    wad_n1 ({((0:ℤ),(0:ℤ)),(1,0)} : Finset Cell)
      - wad_n3 ({((0:ℤ),(0:ℤ)),(1,0)} : Finset Cell) = 4 :=
  wad_defect_eq_four euc_buildable_domino wad_n2d_domino




theorem wad_n1_Ltromino : wad_n1 ({((0:ℤ),(0:ℤ)),(1,0),(0,1)} : Finset Cell) = 5 := by
  unfold wad_n1; decide
theorem wad_n3_Ltromino : wad_n3 ({((0:ℤ),(0:ℤ)),(1,0),(0,1)} : Finset Cell) = 1 := by
  unfold wad_n3; decide
theorem wad_n2d_Ltromino : wad_n2d ({((0:ℤ),(0:ℤ)),(1,0),(0,1)} : Finset Cell) = 0 := by
  unfold wad_n2d; decide

theorem wad_witness_Ltromino :
    wad_n1 ({((0:ℤ),(0:ℤ)),(1,0),(0,1)} : Finset Cell)
      - wad_n3 ({((0:ℤ),(0:ℤ)),(1,0),(0,1)} : Finset Cell) = 4 :=
  wad_defect_eq_four euc_buildable_Ltromino wad_n2d_Ltromino




theorem wad_witness_holeyRing :
    wad_n1 ({((0:ℤ),(0:ℤ)),(1,0),(2,0),(0,1),(2,1),(0,2),(1,2),(2,2)} : Finset Cell)
      - wad_n3 ({((0:ℤ),(0:ℤ)),(1,0),(2,0),(0,1),(2,1),(0,2),(1,2),(2,2)} : Finset Cell)
      - 2 * wad_n2d ({((0:ℤ),(0:ℤ)),(1,0),(2,0),(0,1),(2,1),(0,2),(1,2),(2,2)} : Finset Cell)
      = 0 := by
  rw [wad_defect_eq_four_chi_counts, euc_chi_holeyRing]; ring

end StatMech.Wad
