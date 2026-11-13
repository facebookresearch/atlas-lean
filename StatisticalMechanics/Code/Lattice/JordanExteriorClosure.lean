/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.CrossingParity
import Code.RSW.Defs
import Code.Lattice.TwoPathsCrossWinding

open Set SimpleGraph

namespace StatMech

namespace Lattice

open StatMech.RSW.Box





def jec_quad (z : Site 2) : Set (Site 2) := {p | p 0 ≤ z 0 - 1 ∧ p 1 ≤ z 1 - 1}

@[simp] theorem jec_mem_quad (z p : Site 2) :
    p ∈ jec_quad z ↔ p 0 ≤ z 0 - 1 ∧ p 1 ≤ z 1 - 1 := Iff.rfl




def jec_rayEdge (z : Site 2) (e : Sym2 (Site 2)) : Prop := by
  classical
  exact Sym2.lift ⟨fun x y =>
      (x 0 = y 0 ∧ x 0 ≤ z 0 - 1) ∧
      ((x 1 = z 1 - 1 ∧ y 1 = z 1) ∨ (y 1 = z 1 - 1 ∧ x 1 = z 1)), by
    intro x y; simp only [eq_iff_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1.symm, h1 ▸ h2⟩, by tauto⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1.symm, h1 ▸ h2⟩, by tauto⟩⟩ e

@[simp] theorem jec_rayEdge_mk (z x y : Site 2) :
    jec_rayEdge z s(x, y) ↔
      (x 0 = y 0 ∧ x 0 ≤ z 0 - 1) ∧
      ((x 1 = z 1 - 1 ∧ y 1 = z 1) ∨ (y 1 = z 1 - 1 ∧ x 1 = z 1)) := by
  unfold jec_rayEdge; rfl




def jec_wallEdge (z : Site 2) (e : Sym2 (Site 2)) : Prop := by
  classical
  exact Sym2.lift ⟨fun x y =>
      (x 1 = y 1 ∧ x 1 ≤ z 1 - 1) ∧
      ((x 0 = z 0 - 1 ∧ y 0 = z 0) ∨ (y 0 = z 0 - 1 ∧ x 0 = z 0)), by
    intro x y; simp only [eq_iff_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1.symm, h1 ▸ h2⟩, by tauto⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1.symm, h1 ▸ h2⟩, by tauto⟩⟩ e

@[simp] theorem jec_wallEdge_mk (z x y : Site 2) :
    jec_wallEdge z s(x, y) ↔
      (x 1 = y 1 ∧ x 1 ≤ z 1 - 1) ∧
      ((x 0 = z 0 - 1 ∧ y 0 = z 0) ∨ (y 0 = z 0 - 1 ∧ x 0 = z 0)) := by
  unfold jec_wallEdge; rfl




theorem jec_quad_bdEdge_iff (z u v : Site 2) (hadj : (hypercubicLattice 2).Adj u v) :
    bdEdge (jec_quad z) s(u, v) ↔ (jec_rayEdge z s(u, v) ∨ jec_wallEdge z s(u, v)) := by
  rw [bdEdge_mk, jec_rayEdge_mk, jec_wallEdge_mk]
  simp only [jec_mem_quad]
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  omega



theorem jec_ray_wall_excl (z u v : Site 2) :
    ¬ (jec_rayEdge z s(u, v) ∧ jec_wallEdge z s(u, v)) := by
  rw [jec_rayEdge_mk, jec_wallEdge_mk]; omega



open Classical in



noncomputable def jec_rayCount (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) : ℕ :=
  w.edges.countP (fun e => decide (jec_rayEdge z e))

open Classical in



noncomputable def jec_wallCount (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) : ℕ :=
  w.edges.countP (fun e => decide (jec_wallEdge z e))

@[simp] theorem jec_rayCount_nil (z x : Site 2) :
    jec_rayCount z (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk x x) = 0 := by
  classical simp [jec_rayCount]

@[simp] theorem jec_wallCount_nil (z x : Site 2) :
    jec_wallCount z (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk x x) = 0 := by
  classical simp [jec_wallCount]


theorem jec_rayCount_append (z : Site 2) {x y w' : Site 2}
    (p : (hypercubicLattice 2).Walk x y) (q : (hypercubicLattice 2).Walk y w') :
    jec_rayCount z (p.append q) = jec_rayCount z p + jec_rayCount z q := by
  classical
  rw [jec_rayCount, jec_rayCount, jec_rayCount, SimpleGraph.Walk.edges_append,
    List.countP_append]


theorem jec_rayCount_copy (z : Site 2) {x y x' y' : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (hu : x = x') (hv : y = y') :
    jec_rayCount z (w.copy hu hv) = jec_rayCount z w := by
  classical rw [jec_rayCount, jec_rayCount, SimpleGraph.Walk.edges_copy]


theorem jec_rayCount_reverse (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    jec_rayCount z w.reverse = jec_rayCount z w := by
  classical
  rw [jec_rayCount, jec_rayCount, SimpleGraph.Walk.edges_reverse, List.countP_reverse]

private theorem jec_countP_disjoint_split (l : List (Sym2 (Site 2)))
    (Q R : Sym2 (Site 2) → Prop) [DecidablePred Q] [DecidablePred R]
    (hdec : ∀ e ∈ l, ¬ (Q e ∧ R e)) :
    l.countP (fun e => decide (Q e ∨ R e)) =
      l.countP (fun e => decide (Q e)) + l.countP (fun e => decide (R e)) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.countP_cons, List.countP_cons, List.countP_cons]
    have hexcl : ¬ (Q a ∧ R a) := hdec a (List.mem_cons_self ..)
    have ih' := ih (fun e he => hdec e (List.mem_cons_of_mem a he))
    by_cases hQ : Q a <;> by_cases hR : R a <;> simp_all <;> omega





theorem jec_crossCount_quad_decomp (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    crossCount (jec_quad z) w = jec_rayCount z w + jec_wallCount z w := by
  classical
  rw [crossCount, jec_rayCount, jec_wallCount]
  have key : ∀ e ∈ w.edges,
      (decide (bdEdge (jec_quad z) e) = true ↔
        decide (jec_rayEdge z e ∨ jec_wallEdge z e) = true) := by
    intro e he
    obtain ⟨u, v⟩ := e
    have hadj : (hypercubicLattice 2).Adj u v := w.adj_of_mem_edges he
    simp only [decide_eq_true_eq]
    exact jec_quad_bdEdge_iff z u v hadj
  rw [List.countP_congr key]
  refine jec_countP_disjoint_split w.edges (jec_rayEdge z) (jec_wallEdge z) ?_
  intro e _he
  obtain ⟨u, v⟩ := e
  exact jec_ray_wall_excl z u v











theorem jec_rayCount_horizontalStep (z z' : Site 2) (hz'0 : z' 0 = z 0 + 1)
    (hz'1 : z' 1 = z 1) {x y : Site 2} (w : (hypercubicLattice 2).Walk x y)
    (hz : z ∉ w.support) :
    jec_rayCount z' w = jec_rayCount z w := by
  classical
  rw [jec_rayCount, jec_rayCount]
  refine List.countP_congr ?_
  intro e he
  obtain ⟨p, q⟩ := e
  have hadj : (hypercubicLattice 2).Adj p q := w.adj_of_mem_edges he
  have hp : p ∈ w.support := w.fst_mem_support_of_mem_edges he
  have hq : q ∈ w.support := w.snd_mem_support_of_mem_edges he
  simp only [decide_eq_true_eq, jec_rayEdge_mk]
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, ?_⟩, ?_⟩
    · by_contra hcon
      push Not at hcon
      have hp0 : p 0 = z 0 := by omega
      rcases h3 with ⟨hpr, hqr⟩ | ⟨hqr, hpr⟩
      · rw [hz'1] at hqr
        have hq0 : q 0 = z 0 := by omega
        have hq1 : q 1 = z 1 := hqr
        have : q = z := by funext i; fin_cases i <;> assumption
        exact hz (this ▸ hq)
      · rw [hz'1] at hpr
        have hp1 : p 1 = z 1 := hpr
        have : p = z := by funext i; fin_cases i <;> assumption
        exact hz (this ▸ hp)
    · rw [hz'1] at h3; exact h3
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, by omega⟩, by rw [hz'1]; exact h3⟩





theorem jec_wallCount_verticalStep (z z' : Site 2) (hz'0 : z' 0 = z 0)
    (hz'1 : z' 1 = z 1 + 1) {x y : Site 2} (w : (hypercubicLattice 2).Walk x y)
    (hz : z ∉ w.support) :
    jec_wallCount z' w = jec_wallCount z w := by
  classical
  rw [jec_wallCount, jec_wallCount]
  refine List.countP_congr ?_
  intro e he
  obtain ⟨p, q⟩ := e
  have hadj : (hypercubicLattice 2).Adj p q := w.adj_of_mem_edges he
  have hp : p ∈ w.support := w.fst_mem_support_of_mem_edges he
  have hq : q ∈ w.support := w.snd_mem_support_of_mem_edges he
  simp only [decide_eq_true_eq, jec_wallEdge_mk]
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, ?_⟩, ?_⟩
    · by_contra hcon
      push Not at hcon
      have hp1 : p 1 = z 1 := by omega
      rcases h3 with ⟨hpc, hqc⟩ | ⟨hqc, hpc⟩
      · rw [hz'0] at hqc
        have hq1 : q 1 = z 1 := by omega
        have hq0 : q 0 = z 0 := hqc
        have : q = z := by funext i; fin_cases i <;> assumption
        exact hz (this ▸ hq)
      · rw [hz'0] at hpc
        have hp0 : p 0 = z 0 := hpc
        have : p = z := by funext i; fin_cases i <;> assumption
        exact hz (this ▸ hp)
    · rw [hz'0] at h3; exact h3
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, by omega⟩, by rw [hz'0]; exact h3⟩











theorem jec_loop_ray_wall_parity (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) :
    Even (jec_rayCount z Vc) ↔ Even (jec_wallCount z Vc) := by
  have heven : Even (crossCount (jec_quad z) Vc) := crossCount_even_of_loop (jec_quad z) Vc
  rw [jec_crossCount_quad_decomp z Vc, Nat.even_add] at heven
  exact heven








theorem jec_localConstancy {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ Vc.support) (hv : v ∉ Vc.support) :
    (Even (jec_rayCount u Vc) ↔ Even (jec_rayCount v Vc)) := by
  have hadj' := hadj
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj'
  
  by_cases hc0 : u 0 = v 0
  · 
    have hc1 : u 1 = v 1 + 1 ∨ v 1 = u 1 + 1 := by omega
    rcases hc1 with h | h
    · 
      have hwall : jec_wallCount u Vc = jec_wallCount v Vc :=
        jec_wallCount_verticalStep v u (by omega) (by omega) Vc hv
      rw [jec_loop_ray_wall_parity u Vc, jec_loop_ray_wall_parity v Vc, hwall]
    · 
      have hwall : jec_wallCount v Vc = jec_wallCount u Vc :=
        jec_wallCount_verticalStep u v (by omega) (by omega) Vc hu
      rw [jec_loop_ray_wall_parity u Vc, jec_loop_ray_wall_parity v Vc, hwall]
  · 
    have hc0' : u 0 = v 0 + 1 ∨ v 0 = u 0 + 1 := by omega
    rcases hc0' with h | h
    · have hray : jec_rayCount u Vc = jec_rayCount v Vc :=
        jec_rayCount_horizontalStep v u (by omega) (by omega) Vc hv
      rw [hray]
    · have hray : jec_rayCount v Vc = jec_rayCount u Vc :=
        jec_rayCount_horizontalStep u v (by omega) (by omega) Vc hu
      rw [hray]





def jec_leftRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Set (Site 2) :=
  {z | ¬ Even (jec_rayCount z Vc)}

@[simp] theorem jec_mem_leftRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (z : Site 2) : z ∈ jec_leftRegion Vc ↔ ¬ Even (jec_rayCount z Vc) := Iff.rfl





theorem jec_leftRegion_bdEdge_support {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
    u ∈ Vc.support ∨ v ∈ Vc.support := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hu, hv⟩ := hcon
  rw [bdEdge_mk] at hbd
  simp only [jec_mem_leftRegion] at hbd
  
  have hpar := jec_localConstancy Vc hadj hu hv
  tauto








def jec_vsegUp (col : ℤ) : (r : ℤ) → (k : ℕ) →
    (hypercubicLattice 2).Walk ![col, r] ![col, r + (k:ℤ)]
  | r, 0 => (SimpleGraph.Walk.nil).copy rfl (by norm_num)
  | r, (k+1) => by
      have hadj : (hypercubicLattice 2).Adj ![col, r] ![col, r+1] := by
        simp [hypercubicLattice_adj, Fin.sum_univ_two]
      exact (SimpleGraph.Walk.cons hadj (jec_vsegUp col (r+1) k)).copy rfl (by push_cast; ring_nf)



def jec_hsegRight (row : ℤ) : (t : ℤ) → (k : ℕ) →
    (hypercubicLattice 2).Walk ![t, row] ![t + (k:ℤ), row]
  | t, 0 => (SimpleGraph.Walk.nil).copy rfl (by norm_num)
  | t, (k+1) => by
      have hadj : (hypercubicLattice 2).Adj ![t, row] ![t+1, row] := by
        simp [hypercubicLattice_adj, Fin.sum_univ_two]
      exact (SimpleGraph.Walk.cons hadj (jec_hsegRight row (t+1) k)).copy rfl
        (by push_cast; ring_nf)




theorem jec_rayCount_vsegUp (z : Site 2) (col r : ℤ) (k : ℕ) :
    jec_rayCount z (jec_vsegUp col r k) =
      (if col ≤ z 0 - 1 ∧ r ≤ z 1 - 1 ∧ z 1 - 1 ≤ r + (k:ℤ) - 1 then 1 else 0) := by
  classical
  induction k generalizing r with
  | zero =>
    simp only [jec_vsegUp, jec_rayCount, SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_nil,
      List.countP_nil]
    rw [eq_comm, if_neg]; push_cast; omega
  | succ k ih =>
    rw [jec_vsegUp, jec_rayCount, SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_cons,
      List.countP_cons]
    have ihr := ih (r+1)
    rw [jec_rayCount] at ihr
    rw [ihr]
    have hhead : (decide (jec_rayEdge z s(![col, r], ![col, r+1]))) =
        decide (col ≤ z 0 - 1 ∧ r = z 1 - 1) := by
      rw [decide_eq_decide]
      simp only [jec_rayEdge_mk, Matrix.cons_val_zero, Matrix.cons_val_one, true_and]
      omega
    rw [hhead]
    simp only [decide_eq_true_eq]
    push_cast
    split_ifs <;> omega



theorem jec_rayCount_hsegRight (z : Site 2) (row t : ℤ) (k : ℕ) :
    jec_rayCount z (jec_hsegRight row t k) = 0 := by
  classical
  induction k generalizing t with
  | zero =>
    simp only [jec_hsegRight, jec_rayCount, SimpleGraph.Walk.edges_copy,
      SimpleGraph.Walk.edges_nil, List.countP_nil]
  | succ k ih =>
    rw [jec_hsegRight, jec_rayCount, SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_cons,
      List.countP_cons]
    have ihr := ih (t+1)
    rw [jec_rayCount] at ihr
    rw [ihr]
    have hhead : ¬ jec_rayEdge z s(![t, row], ![t+1, row]) := by
      rw [jec_rayEdge_mk]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    rw [decide_eq_false hhead]; simp


theorem jec_vsegUp_support (col r : ℤ) (k : ℕ) {p : Site 2}
    (hp : p ∈ (jec_vsegUp col r k).support) :
    p 0 = col ∧ r ≤ p 1 ∧ p 1 ≤ r + (k:ℤ) := by
  induction k generalizing r with
  | zero =>
    rw [jec_vsegUp, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_nil] at hp
    rw [List.mem_singleton] at hp; subst hp
    refine ⟨rfl, ?_, ?_⟩ <;> simp
  | succ k ih =>
    rw [jec_vsegUp, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_cons,
      List.mem_cons] at hp
    rcases hp with hp | hp
    · subst hp
      refine ⟨rfl, by simp, ?_⟩
      simp only [Matrix.cons_val_one]; push_cast; omega
    · obtain ⟨h0, h1, h2⟩ := ih (r+1) hp
      refine ⟨h0, by omega, by push_cast at h2 ⊢; omega⟩



theorem jec_hsegRight_support (row t : ℤ) (k : ℕ) {p : Site 2}
    (hp : p ∈ (jec_hsegRight row t k).support) :
    p 1 = row ∧ t ≤ p 0 ∧ p 0 ≤ t + (k:ℤ) := by
  induction k generalizing t with
  | zero =>
    rw [jec_hsegRight, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_nil] at hp
    rw [List.mem_singleton] at hp; subst hp
    refine ⟨rfl, ?_, ?_⟩ <;> simp
  | succ k ih =>
    rw [jec_hsegRight, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_cons,
      List.mem_cons] at hp
    rcases hp with hp | hp
    · subst hp
      refine ⟨rfl, by simp, ?_⟩
      simp only [Matrix.cons_val_zero]; push_cast; omega
    · obtain ⟨h1, h0a, h0b⟩ := ih (t+1) hp
      refine ⟨h1, by omega, by push_cast at h0b ⊢; omega⟩










def jec_retPath (α a0 b0 c d : ℤ) (_ha : α ≤ a0) (_hb : α ≤ b0) (_hcd : c ≤ d) :
    (hypercubicLattice 2).Walk ![b0, d] ![a0, c] :=
  let s1 : (hypercubicLattice 2).Walk ![b0, d] ![b0, d+1] :=
    (jec_vsegUp b0 d 1).copy rfl (by ext i; fin_cases i <;> simp)
  let s2 : (hypercubicLattice 2).Walk ![b0, d+1] ![α-1, d+1] :=
    ((jec_hsegRight (d+1) (α-1) (b0-(α-1)).toNat).copy rfl
      (by ext i; fin_cases i <;> (simp; try omega))).reverse
  let s3 : (hypercubicLattice 2).Walk ![α-1, d+1] ![α-1, c-1] :=
    ((jec_vsegUp (α-1) (c-1) (d+1-(c-1)).toNat).copy rfl
      (by ext i; fin_cases i <;> (simp; try omega))).reverse
  let s4 : (hypercubicLattice 2).Walk ![α-1, c-1] ![a0, c-1] :=
    (jec_hsegRight (c-1) (α-1) (a0-(α-1)).toNat).copy rfl
      (by ext i; fin_cases i <;> (simp; try omega))
  let s5 : (hypercubicLattice 2).Walk ![a0, c-1] ![a0, c] :=
    (jec_vsegUp a0 (c-1) 1).copy rfl (by ext i; fin_cases i <;> simp)
  s1.append (s2.append (s3.append (s4.append s5)))





theorem jec_rayCount_retPath (z : Site 2) (α a0 b0 c d : ℤ)
    (ha : α ≤ a0) (hb : α ≤ b0) (hcd : c ≤ d) :
    jec_rayCount z (jec_retPath α a0 b0 c d ha hb hcd) =
      (if b0 ≤ z 0 - 1 ∧ d ≤ z 1 - 1 ∧ z 1 - 1 ≤ d then 1 else 0)
      + (if α-1 ≤ z 0 - 1 ∧ c-1 ≤ z 1 - 1 ∧
            z 1 - 1 ≤ (c-1) + ((d+1-(c-1)).toNat:ℤ) - 1 then 1 else 0)
      + (if a0 ≤ z 0 - 1 ∧ c-1 ≤ z 1 - 1 ∧ z 1 - 1 ≤ c-1 then 1 else 0) := by
  unfold jec_retPath
  simp only [jec_rayCount_append, jec_rayCount_copy, jec_rayCount_reverse, jec_rayCount_vsegUp,
    jec_rayCount_hsegRight]
  push_cast
  have e1 : (if b0 ≤ z 0 - 1 ∧ d ≤ z 1 - 1 ∧ z 1 - 1 ≤ d + (1:ℤ) - 1 then (1:ℕ) else 0)
      = (if b0 ≤ z 0 - 1 ∧ d ≤ z 1 - 1 ∧ z 1 - 1 ≤ d then 1 else 0) := by
    congr 1; apply propext; constructor <;> (rintro ⟨a, b, c⟩; exact ⟨a, b, by omega⟩)
  have e3 : (if a0 ≤ z 0 - 1 ∧ c - 1 ≤ z 1 - 1 ∧ z 1 - 1 ≤ c - 1 + (1:ℤ) - 1 then (1:ℕ) else 0)
      = (if a0 ≤ z 0 - 1 ∧ c - 1 ≤ z 1 - 1 ∧ z 1 - 1 ≤ c - 1 then 1 else 0) := by
    congr 1; apply propext; constructor <;> (rintro ⟨a, b, c⟩; exact ⟨a, b, by omega⟩)
  rw [e1, e3]; ring





theorem jec_retPath_support (α a0 b0 c d : ℤ) (ha : α ≤ a0) (hb : α ≤ b0) (hcd : c ≤ d)
    {p : Site 2} (hp : p ∈ (jec_retPath α a0 b0 c d ha hb hcd).support) :
    p 0 = α - 1 ∨ p 1 = c - 1 ∨ p 1 = d + 1 ∨ p = ![b0, d] ∨ p = ![a0, c] := by
  unfold jec_retPath at hp
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse] at hp
  rcases hp with h | h | h | h | h
  · obtain ⟨h0, h1, h2⟩ := jec_vsegUp_support b0 d 1 h
    push_cast at h2
    by_cases hpd : p 1 = d + 1
    · right; right; left; exact hpd
    · right; right; right; left
      have hp1 : p 1 = d := by omega
      ext i; fin_cases i
      · simpa using h0
      · simpa using hp1
  · obtain ⟨h1, _, _⟩ := jec_hsegRight_support (d+1) (α-1) _ h
    right; right; left; exact h1
  · obtain ⟨h0, _, _⟩ := jec_vsegUp_support (α-1) (c-1) _ h
    left; exact h0
  · obtain ⟨h1, _, _⟩ := jec_hsegRight_support (c-1) (α-1) _ h
    right; left; exact h1
  · obtain ⟨h0, h1, h2⟩ := jec_vsegUp_support a0 (c-1) 1 h
    push_cast at h2
    by_cases hpc : p 1 = c - 1
    · right; left; exact hpc
    · right; right; right; right
      have hp1 : p 1 = c := by omega
      ext i; fin_cases i
      · simpa using h0
      · simpa using hp1



theorem jec_retPath_col (α β a0 b0 c d : ℤ) (ha : α ≤ a0) (hb : α ≤ b0) (hcd : c ≤ d)
    (haβ : a0 ≤ β) (hbβ : b0 ≤ β) (hαβ : α ≤ β) {p : Site 2}
    (hp : p ∈ (jec_retPath α a0 b0 c d ha hb hcd).support) :
    α - 1 ≤ p 0 ∧ p 0 ≤ β := by
  unfold jec_retPath at hp
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse] at hp
  rcases hp with h | h | h | h | h
  · obtain ⟨h0, _, _⟩ := jec_vsegUp_support b0 d 1 h; omega
  · obtain ⟨_, h0a, h0b⟩ := jec_hsegRight_support (d+1) (α-1) _ h
    rw [show ((b0 - (α-1)).toNat : ℤ) = b0 - (α-1) by omega] at h0b; omega
  · obtain ⟨h0, _, _⟩ := jec_vsegUp_support (α-1) (c-1) _ h; omega
  · obtain ⟨_, h0a, h0b⟩ := jec_hsegRight_support (c-1) (α-1) _ h
    rw [show ((a0 - (α-1)).toNat : ℤ) = a0 - (α-1) by omega] at h0b; omega
  · obtain ⟨h0, _, _⟩ := jec_vsegUp_support a0 (c-1) 1 h; omega








def jec_belowSet (y : ℤ) : Set (Site 2) := {p | p 1 ≤ y - 1}

@[simp] theorem jec_mem_belowSet (y : ℤ) (p : Site 2) :
    p ∈ jec_belowSet y ↔ p 1 ≤ y - 1 := Iff.rfl



theorem jec_belowSet_bdEdge (y : ℤ) (u v : Site 2) (hadj : (hypercubicLattice 2).Adj u v) :
    bdEdge (jec_belowSet y) s(u, v) ↔
      (u 0 = v 0) ∧ ((u 1 = y - 1 ∧ v 1 = y) ∨ (v 1 = y - 1 ∧ u 1 = y)) := by
  rw [bdEdge_mk]; simp only [jec_mem_belowSet]
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  omega





theorem jec_ray_eq_below (z : Site 2) {x y : Site 2} (w : (hypercubicLattice 2).Walk x y)
    (hfar : ∀ p ∈ w.support, p 0 ≤ z 0 - 1) :
    jec_rayCount z w = crossCount (jec_belowSet (z 1)) w := by
  classical
  rw [jec_rayCount, crossCount]
  refine List.countP_congr ?_
  intro e he
  obtain ⟨u, v⟩ := e
  have hadj : (hypercubicLattice 2).Adj u v := w.adj_of_mem_edges he
  have hcu := hfar u (w.fst_mem_support_of_mem_edges he)
  have hcv := hfar v (w.snd_mem_support_of_mem_edges he)
  simp only [decide_eq_true_eq]
  show jec_rayEdge z s(u, v) ↔ bdEdge (jec_belowSet (z 1)) s(u, v)
  rw [jec_rayEdge_mk, jec_belowSet_bdEdge (z 1) u v hadj]
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩




theorem jec_ray_even_far {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (z : Site 2)
    (hfar : ∀ p ∈ Vc.support, p 0 ≤ z 0 - 1) :
    Even (jec_rayCount z Vc) := by
  rw [jec_ray_eq_below z Vc hfar]
  exact crossCount_even_of_loop (jec_belowSet (z 1)) Vc




theorem jec_rayCount_eq_zero_of_right (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (h : ∀ p ∈ w.support, z 0 ≤ p 0) :
    jec_rayCount z w = 0 := by
  classical
  rw [jec_rayCount, List.countP_eq_zero]
  intro e he
  obtain ⟨u, v⟩ := e
  have hu := h u (w.fst_mem_support_of_mem_edges he)
  simp only [decide_eq_true_eq]
  show ¬ jec_rayEdge z s(u, v)
  rw [jec_rayEdge_mk]
  omega


























theorem jec_arcSeparatingSet (α β c d a0 b0 : ℤ)
    (hαβ : α < β) (hcd : c ≤ d)
    (ha0 : α ≤ a0) (ha0' : a0 ≤ β) (hb0 : α ≤ b0) (hb0' : b0 ≤ β)
    (V : (hypercubicLattice 2).Walk ![a0, c] ![b0, d])
    (hVbox : ∀ p ∈ V.support, p ∈ rect α β c d)
    (P : Set (Site 2)) (hVP : ∀ p ∈ V.support, p ∈ P) :
    ArcSeparatingSet P α β c d := by
  classical
  
  set R := jec_retPath α a0 b0 c d ha0 hb0 hcd with hR
  set Vc : (hypercubicLattice 2).Walk ![a0, c] ![a0, c] := V.append R with hVc
  
  have ha_mem : (![a0, c] : Site 2) ∈ V.support := V.start_mem_support
  have hb_mem : (![b0, d] : Site 2) ∈ V.support := V.end_mem_support
  
  have hVcol : ∀ p ∈ V.support, α ≤ p 0 ∧ p 0 ≤ β ∧ c ≤ p 1 ∧ p 1 ≤ d := by
    intro p hp; exact hVbox p hp
  
  have hVccol : ∀ p ∈ Vc.support, p 0 ≤ β := by
    intro p hp
    rw [hVc, SimpleGraph.Walk.mem_support_append_iff] at hp
    rcases hp with h | h
    · exact (hVcol p h).2.1
    · exact (jec_retPath_col α β a0 b0 c d ha0 hb0 hcd ha0' hb0' (le_of_lt hαβ) h).2
  
  have hRbox : ∀ p ∈ R.support, p ∈ rect α β c d → p ∈ V.support := by
    intro p hpR hpbox
    rw [mem_rect] at hpbox
    rcases jec_retPath_support α a0 b0 c d ha0 hb0 hcd hpR with h | h | h | h | h
    · omega 
    · omega 
    · omega 
    · rw [h]; exact hb_mem  
    · rw [h]; exact ha_mem  
  
  have hVcbox : ∀ p ∈ Vc.support, p ∈ rect α β c d → p ∈ V.support := by
    intro p hp hpbox
    rw [hVc, SimpleGraph.Walk.mem_support_append_iff] at hp
    rcases hp with h | h
    · exact h
    · exact hRbox p h hpbox
  
  refine ⟨jec_leftRegion Vc \ {z | z 0 = β ∧ z ∈ V.support}, ?_, ?_, ?_⟩
  · 
    intro z hzbox hzα
    rw [mem_rect] at hzbox
    refine ⟨?_, ?_⟩
    · 
      rw [jec_mem_leftRegion, hVc, jec_rayCount_append]
      have hV0 : jec_rayCount z V = 0 := by
        refine jec_rayCount_eq_zero_of_right z V ?_
        intro p hp; rw [hzα]; exact (hVcol p hp).1
      have hRray : jec_rayCount z R = 1 := by
        rw [hR, jec_rayCount_retPath]
        rw [if_neg (by rw [hzα]; omega), if_pos ?_, if_neg (by rw [hzα]; omega)]
        rw [hzα]
        refine ⟨by omega, by omega, ?_⟩
        rw [show ((d+1-(c-1)).toNat : ℤ) = d+1-(c-1) by omega]; omega
      rw [hV0, hRray]; decide
    · 
      simp only [Set.mem_setOf_eq, not_and]
      intro hzβ; omega
  · 
    intro z hzbox hzβ
    rw [mem_rect] at hzbox
    rw [Set.mem_diff]
    rintro ⟨hzleft, hzrem⟩
    
    by_cases hzV : z ∈ V.support
    · 
      exact hzrem ⟨hzβ, hzV⟩
    · 
      have hzVc : z ∉ Vc.support := by
        rw [hVc, SimpleGraph.Walk.mem_support_append_iff]
        rintro (h | h)
        · exact hzV h
        · exact hzV (hRbox z h (by rw [mem_rect]; exact hzbox))
      
      have hz'0 : (![z 0 + 1, z 1] : Site 2) 0 = z 0 + 1 := by simp
      have hz'1 : (![z 0 + 1, z 1] : Site 2) 1 = z 1 := by simp
      have hray_eq : jec_rayCount (![z 0 + 1, z 1] : Site 2) Vc = jec_rayCount z Vc :=
        jec_rayCount_horizontalStep z (![z 0 + 1, z 1]) hz'0 hz'1 Vc hzVc
      have hfar : ∀ p ∈ Vc.support, p 0 ≤ (![z 0 + 1, z 1] : Site 2) 0 - 1 := by
        intro p hp; have := hVccol p hp; rw [hz'0, hzβ]; omega
      have heven : Even (jec_rayCount z Vc) := by
        rw [← hray_eq]; exact jec_ray_even_far Vc (![z 0 + 1, z 1]) hfar
      rw [jec_mem_leftRegion] at hzleft
      exact hzleft heven
  · 
    intro u v hubox hvbox hadj hbd
    
    rw [bdEdge_mk] at hbd
    
    have key : ∀ x' y' : Site 2, x' ∈ rect α β c d → y' ∈ rect α β c d →
        (hypercubicLattice 2).Adj x' y' →
        x' ∈ jec_leftRegion Vc \ {z | z 0 = β ∧ z ∈ V.support} →
        y' ∉ jec_leftRegion Vc \ {z | z 0 = β ∧ z ∈ V.support} →
        x' ∈ V.support ∨ y' ∈ V.support := by
      intro x' y' hx'box hy'box hadj' hx'S hy'S
      rw [Set.mem_diff] at hx'S
      obtain ⟨hx'left, _hx'rem⟩ := hx'S
      rw [Set.mem_diff, not_and_or, not_not] at hy'S
      rcases hy'S with hy'left | hy'rem
      · 
        have hbdL : bdEdge (jec_leftRegion Vc) s(x', y') := by
          rw [bdEdge_mk]; exact ⟨fun _ => hy'left, fun _ => hx'left⟩
        rcases jec_leftRegion_bdEdge_support Vc hadj' hbdL with hsupp | hsupp
        · exact Or.inl (hVcbox x' hsupp hx'box)
        · exact Or.inr (hVcbox y' hsupp hy'box)
      · 
        exact Or.inr hy'rem.2
    
    by_cases huS : u ∈ jec_leftRegion Vc \ {z | z 0 = β ∧ z ∈ V.support}
    · have hvS : v ∉ jec_leftRegion Vc \ {z | z 0 = β ∧ z ∈ V.support} := hbd.mp huS
      rcases key u v hubox hvbox hadj huS hvS with h | h
      · exact Or.inl (hVP u h)
      · exact Or.inr (hVP v h)
    · 
      have hvS : v ∈ jec_leftRegion Vc \ {z | z 0 = β ∧ z ∈ V.support} := by
        by_contra hvS
        exact huS (hbd.mpr hvS)
      rcases key v u hvbox hubox hadj.symm hvS huS with h | h
      · exact Or.inr (hVP v h)
      · exact Or.inl (hVP u h)










open StatMech.Universality in





theorem jec_vsFix_arc_sides (ω : ConfigSpace (Sym2 (Site 2))) {α β m m' c d : ℤ}
    (hαβ : α < β) (hcd : c ≤ d) :
    StatMech.Universality.vsFix_arc_sides ω α β m m' c d := by
  intro hαm hmm' hm'β xB hxB hxBbot yT hyT hcV
  
  obtain ⟨V, hVsupp⟩ := tpc_arcWalk_support hxB (topSide_subset hyT) hcV
  
  have hxB1 : xB 1 = c := hxBbot.2
  have hyT1 : yT 1 = d := hyT.2
  have hxBrect : xB ∈ rect m m' c d := hxB
  have hyTrect : yT ∈ rect m m' c d := topSide_subset hyT
  
  have hxBeq : xB = ![xB 0, c] := by ext i; fin_cases i <;> simp [hxB1]
  have hyTeq : yT = ![yT 0, d] := by ext i; fin_cases i <;> simp [hyT1]
  set V' : (hypercubicLattice 2).Walk ![xB 0, c] ![yT 0, d] := V.copy hxBeq hyTeq with hV'
  
  have hV'supp : ∀ p ∈ V'.support, p ∈ overlapComp ω m m' c d xB hxB := by
    intro p hp; rw [hV', SimpleGraph.Walk.support_copy] at hp; exact hVsupp p hp
  have hV'box : ∀ p ∈ V'.support, p ∈ rect α β c d := by
    intro p hp
    have hpO : p ∈ rect m m' c d := (hV'supp p hp).1
    rw [mem_rect] at hpO ⊢; omega
  
  have ha0 : α ≤ xB 0 := by rw [mem_rect] at hxBrect; omega
  have ha0' : xB 0 ≤ β := by rw [mem_rect] at hxBrect; omega
  have hb0 : α ≤ yT 0 := by rw [mem_rect] at hyTrect; omega
  have hb0' : yT 0 ≤ β := by rw [mem_rect] at hyTrect; omega
  
  exact jec_arcSeparatingSet α β c d (xB 0) (yT 0) hαβ hcd ha0 ha0' hb0 hb0'
    V' hV'box (overlapComp ω m m' c d xB hxB) hV'supp







theorem jec_rsw_strip_glue
    (μ : MeasureTheory.Measure (ConfigSpace (Sym2 (Site 2))))
    [MeasureTheory.IsProbabilityMeasure μ]
    (hpa : StatMech.Universality.PositivelyAssociated μ) {a m m' b c d : ℤ}
    (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (hamL : a < m') (hmbR : m < b) (hcd : c ≤ d) :
    μ.real (horizontalCrossingEvent a m' c d)
        * μ.real (verticalCrossingEvent m m' c d)
        * μ.real (horizontalCrossingEvent m b c d)
      ≤ μ.real (horizontalCrossingEvent a b c d) :=
  StatMech.Universality.vsFix_rsw_strip_glue_of_arc_sides μ hpa ham hmm' hm'b
    (fun ω => jec_vsFix_arc_sides ω hamL hcd)
    (fun ω => jec_vsFix_arc_sides ω hmbR hcd)

end Lattice

end StatMech
