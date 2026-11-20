/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































































import Mathlib
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.OrbitWindingWitness
import Code.Lattice.WindingWitness
import Code.Walls.kwceventtocut

open Set SimpleGraph
open scoped BigOperators

namespace StatMech

namespace Walls

open StatMech.Lattice












def rpc_hCrossEdge (u : Site 2) : Sym2 (Site 2) :=
  s(![u 0, u 1 - 1], ![u 0, u 1])

@[simp] theorem rpc_hCrossEdge_isRayEdge_left (u : Site 2) :
    ¬ jec_rayEdge u (rpc_hCrossEdge u) := by
  rw [rpc_hCrossEdge, jec_rayEdge_mk]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  omega




theorem rpc_hCrossEdge_isRayEdge_right (u v : Site 2) (h0 : v 0 = u 0 + 1)
    (h1 : v 1 = u 1) : jec_rayEdge v (rpc_hCrossEdge u) := by
  rw [rpc_hCrossEdge, jec_rayEdge_mk]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  refine ⟨⟨trivial, by omega⟩, Or.inl ⟨by omega, by omega⟩⟩







theorem rpc_rayEdge_horizontalStep (u v : Site 2) (h0 : v 0 = u 0 + 1) (h1 : v 1 = u 1)
    {p q : Site 2} (_hadj : (hypercubicLattice 2).Adj p q) :
    jec_rayEdge v s(p, q) ↔ (jec_rayEdge u s(p, q) ∨ s(p, q) = rpc_hCrossEdge u) := by
  rw [jec_rayEdge_mk, jec_rayEdge_mk, rpc_hCrossEdge, Sym2.eq_iff]
  constructor
  · rintro ⟨⟨hpq0, hp0⟩, hstr⟩
    rcases hstr with ⟨hp1, hq1⟩ | ⟨hq1, hp1⟩
    · 
      by_cases hlt : p 0 ≤ u 0 - 1
      · exact Or.inl ⟨⟨hpq0, hlt⟩, Or.inl ⟨by omega, by omega⟩⟩
      · 
        have hp0e : p 0 = u 0 := by omega
        have hq0e : q 0 = u 0 := by omega
        have hp1e : p 1 = u 1 - 1 := by omega
        have hq1e : q 1 = u 1 := by omega
        right; left
        constructor <;> (funext i; fin_cases i) <;> simp_all
    · by_cases hlt : p 0 ≤ u 0 - 1
      · exact Or.inl ⟨⟨hpq0, hlt⟩, Or.inr ⟨by omega, by omega⟩⟩
      · have hp0e : p 0 = u 0 := by omega
        have hq0e : q 0 = u 0 := by omega
        have hp1e : p 1 = u 1 := by omega
        have hq1e : q 1 = u 1 - 1 := by omega
        right; right
        constructor <;> (funext i; fin_cases i) <;> simp_all
  · rintro (⟨⟨hpq0, hp0⟩, hstr⟩ | hcross)
    · refine ⟨⟨hpq0, by omega⟩, ?_⟩
      rcases hstr with ⟨hp1, hq1⟩ | ⟨hq1, hp1⟩
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · 
      rcases hcross with ⟨hp, hq⟩ | ⟨hp, hq⟩
      · refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [hp, hq]; simp only [Matrix.cons_val_zero]
        · rw [hp]; simp only [Matrix.cons_val_zero]; omega
        · left; constructor
          · rw [hp]; simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega
          · rw [hq]; simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega
      · refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [hp, hq]; simp only [Matrix.cons_val_zero]
        · rw [hp]; simp only [Matrix.cons_val_zero]; omega
        · right; constructor
          · rw [hq]; simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega
          · rw [hp]; simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega








open Classical in





theorem rpc_rayCount_edges_split (u v : Site 2) (h0 : v 0 = u 0 + 1) (h1 : v 1 = u 1)
    (l : List (Sym2 (Site 2))) (hl : ∀ e ∈ l, ∃ p q, e = s(p, q) ∧ (hypercubicLattice 2).Adj p q) :
    l.countP (fun e => decide (jec_rayEdge v e)) =
      l.countP (fun e => decide (jec_rayEdge u e)) + l.count (rpc_hCrossEdge u) := by
  classical
  induction l with
  | nil => simp
  | cons a t ih =>
    have ih' := ih (fun e he => hl e (List.mem_cons_of_mem a he))
    obtain ⟨p, q, rfl, hadj⟩ := hl a (List.mem_cons_self ..)
    rw [List.countP_cons, List.countP_cons, List.count_cons]
    have hdich := rpc_rayEdge_horizontalStep u v h0 h1 hadj
    have hexcl : ¬ (jec_rayEdge u s(p, q) ∧ s(p, q) = rpc_hCrossEdge u) := by
      rintro ⟨hru, heq⟩
      exact rpc_hCrossEdge_isRayEdge_left u (heq ▸ hru)
    by_cases hru : jec_rayEdge u s(p, q)
    · have hrv : jec_rayEdge v s(p, q) := hdich.mpr (Or.inl hru)
      have hne : s(p, q) ≠ rpc_hCrossEdge u := fun h => hexcl ⟨hru, h⟩
      rw [if_pos (by simp [hrv]), if_pos (by simp [hru])]
      rw [ih']; simp only [beq_iff_eq, hne, ite_false]; omega
    · by_cases hcross : s(p, q) = rpc_hCrossEdge u
      · have hrv : jec_rayEdge v s(p, q) := hdich.mpr (Or.inr hcross)
        rw [if_pos (by simp [hrv]), if_neg (by simp [hru])]
        rw [ih']; simp only [beq_iff_eq, hcross, if_pos]; omega
      · have hrv : ¬ jec_rayEdge v s(p, q) := by
          intro h; rcases hdich.mp h with h' | h'
          · exact hru h'
          · exact hcross h'
        rw [if_neg (by simp [hrv]), if_neg (by simp [hru])]
        rw [ih']; simp only [beq_iff_eq, hcross, ite_false]; omega











theorem rpc_rayCount_horizontalStep_diff {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (u v : Site 2) (h0 : v 0 = u 0 + 1) (h1 : v 1 = u 1) :
    jec_rayCount v Vc = jec_rayCount u Vc + Vc.edges.count (rpc_hCrossEdge u) := by
  classical
  rw [jec_rayCount, jec_rayCount]
  exact rpc_rayCount_edges_split u v h0 h1 Vc.edges (fun e he => by
    obtain ⟨p, q⟩ := e
    exact ⟨p, q, rfl, Vc.adj_of_mem_edges he⟩)






theorem rpc_horizontalFlip_iff {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (u v : Site 2) (h0 : v 0 = u 0 + 1) (h1 : v 1 = u 1) :
    (Even (jec_rayCount u Vc) ↔ ¬ Even (jec_rayCount v Vc)) ↔
      Odd (Vc.edges.count (rpc_hCrossEdge u)) := by
  rw [rpc_rayCount_horizontalStep_diff Vc u v h0 h1, Nat.even_add,
    ← Nat.not_even_iff_odd]
  by_cases hu : Even (jec_rayCount u Vc) <;>
    by_cases hc : Even (Vc.edges.count (rpc_hCrossEdge u)) <;>
    simp only [hu, hc, iff_true, iff_false, not_true, not_false_iff]













def rpc_vCrossEdge (u : Site 2) : Sym2 (Site 2) :=
  s(![u 0 - 1, u 1], ![u 0, u 1])

theorem rpc_vCrossEdge_isWallEdge_left (u : Site 2) : ¬ jec_wallEdge u (rpc_vCrossEdge u) := by
  rw [rpc_vCrossEdge, jec_wallEdge_mk]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  omega




theorem rpc_wallEdge_verticalStep (u v : Site 2) (h0 : v 0 = u 0) (h1 : v 1 = u 1 + 1)
    {p q : Site 2} (_hadj : (hypercubicLattice 2).Adj p q) :
    jec_wallEdge v s(p, q) ↔ (jec_wallEdge u s(p, q) ∨ s(p, q) = rpc_vCrossEdge u) := by
  rw [jec_wallEdge_mk, jec_wallEdge_mk, rpc_vCrossEdge, Sym2.eq_iff]
  constructor
  · rintro ⟨⟨hpq1, hp1⟩, hstr⟩
    rcases hstr with ⟨hp0, hq0⟩ | ⟨hq0, hp0⟩
    · by_cases hle : p 1 ≤ u 1 - 1
      · exact Or.inl ⟨⟨hpq1, hle⟩, Or.inl ⟨by omega, by omega⟩⟩
      · have hp1e : p 1 = u 1 := by omega
        have hq1e : q 1 = u 1 := by omega
        have hp0e : p 0 = u 0 - 1 := by omega
        have hq0e : q 0 = u 0 := by omega
        right; left
        constructor <;> (funext i; fin_cases i) <;> simp_all
    · by_cases hle : p 1 ≤ u 1 - 1
      · exact Or.inl ⟨⟨hpq1, hle⟩, Or.inr ⟨by omega, by omega⟩⟩
      · have hp1e : p 1 = u 1 := by omega
        have hq1e : q 1 = u 1 := by omega
        have hp0e : p 0 = u 0 := by omega
        have hq0e : q 0 = u 0 - 1 := by omega
        right; right
        constructor <;> (funext i; fin_cases i) <;> simp_all
  · rintro (⟨⟨hpq1, hp1⟩, hstr⟩ | hcross)
    · refine ⟨⟨hpq1, by omega⟩, ?_⟩
      rcases hstr with ⟨hp0, hq0⟩ | ⟨hq0, hp0⟩
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · rcases hcross with ⟨hp, hq⟩ | ⟨hp, hq⟩
      · refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [hp, hq]; simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
        · rw [hp]; simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega
        · left; constructor
          · rw [hp]; simp only [Matrix.cons_val_zero]; omega
          · rw [hq]; simp only [Matrix.cons_val_zero]; omega
      · refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [hp, hq]; simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
        · rw [hp]; simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega
        · right; constructor
          · rw [hq]; simp only [Matrix.cons_val_zero]; omega
          · rw [hp]; simp only [Matrix.cons_val_zero]; omega

open Classical in

theorem rpc_wallCount_edges_split (u v : Site 2) (h0 : v 0 = u 0) (h1 : v 1 = u 1 + 1)
    (l : List (Sym2 (Site 2))) (hl : ∀ e ∈ l, ∃ p q, e = s(p, q) ∧ (hypercubicLattice 2).Adj p q) :
    l.countP (fun e => decide (jec_wallEdge v e)) =
      l.countP (fun e => decide (jec_wallEdge u e)) + l.count (rpc_vCrossEdge u) := by
  classical
  induction l with
  | nil => simp
  | cons a t ih =>
    have ih' := ih (fun e he => hl e (List.mem_cons_of_mem a he))
    obtain ⟨p, q, rfl, hadj⟩ := hl a (List.mem_cons_self ..)
    rw [List.countP_cons, List.countP_cons, List.count_cons]
    have hdich := rpc_wallEdge_verticalStep u v h0 h1 hadj
    have hexcl : ¬ (jec_wallEdge u s(p, q) ∧ s(p, q) = rpc_vCrossEdge u) := by
      rintro ⟨hwu, heq⟩
      exact rpc_vCrossEdge_isWallEdge_left u (heq ▸ hwu)
    by_cases hwu : jec_wallEdge u s(p, q)
    · have hwv : jec_wallEdge v s(p, q) := hdich.mpr (Or.inl hwu)
      have hne : s(p, q) ≠ rpc_vCrossEdge u := fun h => hexcl ⟨hwu, h⟩
      rw [if_pos (by simp [hwv]), if_pos (by simp [hwu])]
      rw [ih']; simp only [beq_iff_eq, hne, ite_false]; omega
    · by_cases hcross : s(p, q) = rpc_vCrossEdge u
      · have hwv : jec_wallEdge v s(p, q) := hdich.mpr (Or.inr hcross)
        rw [if_pos (by simp [hwv]), if_neg (by simp [hwu])]
        rw [ih']; simp only [beq_iff_eq, hcross, ite_true]; omega
      · have hwv : ¬ jec_wallEdge v s(p, q) := by
          intro h; rcases hdich.mp h with h' | h'
          · exact hwu h'
          · exact hcross h'
        rw [if_neg (by simp [hwv]), if_neg (by simp [hwu])]
        rw [ih']; simp only [beq_iff_eq, hcross, ite_false]; omega



theorem rpc_wallCount_verticalStep_diff {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (u v : Site 2) (h0 : v 0 = u 0) (h1 : v 1 = u 1 + 1) :
    jec_wallCount v Vc = jec_wallCount u Vc + Vc.edges.count (rpc_vCrossEdge u) := by
  classical
  rw [jec_wallCount, jec_wallCount]
  exact rpc_wallCount_edges_split u v h0 h1 Vc.edges (fun e he => by
    obtain ⟨p, q⟩ := e
    exact ⟨p, q, rfl, Vc.adj_of_mem_edges he⟩)






theorem rpc_verticalFlip_iff {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (u v : Site 2) (h0 : v 0 = u 0) (h1 : v 1 = u 1 + 1) :
    (Even (jec_rayCount u Vc) ↔ ¬ Even (jec_rayCount v Vc)) ↔
      Odd (Vc.edges.count (rpc_vCrossEdge u)) := by
  rw [jec_loop_ray_wall_parity u Vc, jec_loop_ray_wall_parity v Vc,
    rpc_wallCount_verticalStep_diff Vc u v h0 h1, Nat.even_add, ← Nat.not_even_iff_odd]
  by_cases hu : Even (jec_wallCount u Vc) <;>
    by_cases hc : Even (Vc.edges.count (rpc_vCrossEdge u)) <;>
    simp only [hu, hc, iff_true, iff_false, not_true, not_false_iff]













noncomputable def rpc_crossEdge (u v : Site 2) : Sym2 (Site 2) := by
  classical
  exact
    if v 0 = u 0 + 1 then rpc_hCrossEdge u
    else if u 0 = v 0 + 1 then rpc_hCrossEdge v
    else if v 1 = u 1 + 1 then rpc_vCrossEdge u
    else rpc_vCrossEdge v










theorem rpc_crossFlip {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v) :
    bdEdge (jec_leftRegion Vc) s(u, v) ↔ Odd (Vc.edges.count (rpc_crossEdge u v)) := by
  have hadj' := hadj
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj'
  rw [bdEdge_mk, jec_mem_leftRegion, jec_mem_leftRegion]
  
  have hrestate : ((¬ Even (jec_rayCount u Vc)) ↔ ¬ ¬ Even (jec_rayCount v Vc)) ↔
      (Even (jec_rayCount u Vc) ↔ ¬ Even (jec_rayCount v Vc)) := by
    constructor <;> intro h <;>
      · by_cases hu : Even (jec_rayCount u Vc) <;> by_cases hv : Even (jec_rayCount v Vc) <;>
          simp_all
  rw [hrestate, rpc_crossEdge]
  by_cases hc0 : v 0 = u 0 + 1
  · rw [if_pos hc0]; exact rpc_horizontalFlip_iff Vc u v hc0 (by omega)
  · rw [if_neg hc0]
    by_cases hc0' : u 0 = v 0 + 1
    · rw [if_pos hc0']
      have hfl := rpc_horizontalFlip_iff Vc v u hc0' (by omega)
      rw [← hfl]
      constructor <;> intro h <;>
        · by_cases hu : Even (jec_rayCount u Vc) <;> by_cases hv : Even (jec_rayCount v Vc) <;>
            simp_all
    · rw [if_neg hc0']
      
      have hv0 : v 0 = u 0 := by omega
      by_cases hc1 : v 1 = u 1 + 1
      · rw [if_pos hc1]; exact rpc_verticalFlip_iff Vc u v hv0 hc1
      · rw [if_neg hc1]
        have hc1' : u 1 = v 1 + 1 := by omega
        have hfl := rpc_verticalFlip_iff Vc v u (by omega) hc1'
        rw [← hfl]
        constructor <;> intro h <;>
          · by_cases hu : Even (jec_rayCount u Vc) <;> by_cases hv : Even (jec_rayCount v Vc) <;>
              simp_all



























def rpc_CrossEdgeOddIffOnWalk {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
    (Odd (Vc.edges.count (rpc_crossEdge u v)) ↔ s(u, v) ∈ Vc.edges)






theorem rpc_leftRegion_bdEdge_iff {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hbridge : rpc_CrossEdgeOddIffOnWalk Vc)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v) :
    bdEdge (jec_leftRegion Vc) s(u, v) ↔ s(u, v) ∈ Vc.edges := by
  rw [rpc_crossFlip Vc hadj]
  exact hbridge hadj






theorem rpc_primalWalkLeftRegionMatch_of_bridge
    (hbridge : ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a),
      rpc_CrossEdgeOddIffOnWalk Vc) :
    kwc_PrimalWalkLeftRegionMatch := by
  intro a Vc u v hadj
  rw [List.mem_toFinset]
  exact ((rpc_leftRegion_bdEdge_iff Vc (hbridge Vc) hadj).symm)













theorem rpc_unitSquare_flip :
    bdEdge (jec_leftRegion wwit_unitSquareLoop) s((![0, 1] : Site 2), (![1, 1] : Site 2)) := by
  rw [bdEdge_mk, jec_mem_leftRegion, jec_mem_leftRegion]
  
  have hodd : ¬ Even (jec_rayCount (![1, 1] : Site 2) wwit_unitSquareLoop) :=
    wwit_unitSquareLoop_inside_odd
  have heven : Even (jec_rayCount (![0, 1] : Site 2) wwit_unitSquareLoop) := by
    have hcount : jec_rayCount (![0, 1] : Site 2) wwit_unitSquareLoop = 0 := by
      unfold wwit_unitSquareLoop
      simp only [jec_rayCount_append, jec_rayCount_copy, jec_rayCount_reverse,
        jec_rayCount_vsegUp, jec_rayCount_hsegRight, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      norm_num
    rw [hcount]; exact ⟨0, rfl⟩
  
  simp only [heven, not_true, hodd, not_false_iff]





theorem rpc_unitSquare_crossEdge_odd :
    Odd (wwit_unitSquareLoop.edges.count
      (rpc_crossEdge (![0, 1] : Site 2) (![1, 1] : Site 2))) := by
  have hadj : (hypercubicLattice 2).Adj (![0, 1] : Site 2) (![1, 1] : Site 2) := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  exact (rpc_crossFlip wwit_unitSquareLoop hadj).mp rpc_unitSquare_flip

end Walls

end StatMech
