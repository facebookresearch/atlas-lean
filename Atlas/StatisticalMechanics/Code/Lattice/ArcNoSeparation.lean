/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.StraightWalk
import Code.Lattice.FiniteComplementConnected
import Code.Lattice.FloodFillConnected

open Set SimpleGraph

namespace StatMech

namespace Lattice







def arcns_OffSupportConnected (B : Set (Site 2)) : Prop :=
  ∀ x y : Site 2, x ∉ B → y ∉ B → (ffc_offSupportLattice B).Reachable x y



theorem arcns_walk_of_connected {B : Set (Site 2)} (h : arcns_OffSupportConnected B)
    {x y : Site 2} (hx : x ∉ B) (hy : y ∉ B) :
    ∃ p : (hypercubicLattice 2).Walk x y, ∀ z ∈ p.support, z ∉ B :=
  (ffc_reachable_iff_offSupportWalk hx).mp (h x y hx hy)














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











def arcns_ReachesFarLeft (B : Set (Site 2)) : Prop :=
  ∃ b : ℤ, (∀ q ∈ B, b ≤ q 0) ∧
    ∀ x : Site 2, x ∉ B → ∃ (z0 : Site 2) (p : (hypercubicLattice 2).Walk x z0),
      (∀ w ∈ p.support, w ∉ B) ∧ z0 0 ≤ b - 1





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












noncomputable def arcns_vlshape (x0 y0 x1 y1 : ℤ) :
    (hypercubicLattice 2).Walk ![x0, y0] ![x1, y1] :=
  (sw_vertSeg x0 y0 y1).append (sw_horizSeg y1 x0 x1)



theorem arcns_vlshape_support (x0 y0 x1 y1 : ℤ) (z : Site 2) :
    z ∈ (arcns_vlshape x0 y0 x1 y1).support
      ↔ (∃ t : ℤ, t ∈ Set.uIcc y0 y1 ∧ z = ![x0, t])
        ∨ (∃ t : ℤ, t ∈ Set.uIcc x0 x1 ∧ z = ![t, y1]) := by
  unfold arcns_vlshape
  rw [Walk.mem_support_append_iff, sw_vertSeg_mem_support, sw_horizSeg_mem_support]




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
  · 
    have hw0 : x 0 = u 0 := by have := congrFun hwu 0; simpa using this
    have hw1 : t = u 1 := by have := congrFun hwu 1; simpa using this
    by_cases hc : x 1 = u 1
    · exact hx0ne hc hw0
    · rw [hr, if_neg hc, Set.uIcc_self, Set.mem_singleton_iff] at ht
      exact hc (by rw [← ht, hw1])
  · 
    have hw1 : r = u 1 := by have := congrFun hwu 1; simpa using this
    exact hru hw1





theorem arcns_singlePoint_connected (u : Site 2) :
    arcns_OffSupportConnected ({u} : Set (Site 2)) :=
  arcns_connected_of_reachesFarLeft (arcns_reachesFarLeft_singlePoint u)





















def arcns_LeafRemovable (S : Set (Site 2)) (u' : Site 2) : Prop :=
  arcns_OffSupportConnected S → arcns_OffSupportConnected (insert u' S)




theorem arcns_connected_insert_of_leafRemovable {S : Set (Site 2)} {u' : Site 2}
    (hres : arcns_LeafRemovable S u') (hS : arcns_OffSupportConnected S) :
    arcns_OffSupportConnected (insert u' S) :=
  hres hS




theorem arcns_cons_support {u v w : Site 2} (h : (hypercubicLattice 2).Adj u v)
    (q : (hypercubicLattice 2).Walk v w) :
    {z : Site 2 | z ∈ (Walk.cons h q).support}
      = insert u {z : Site 2 | z ∈ q.support} := by
  ext z
  simp only [Walk.support_cons, List.mem_cons, Set.mem_setOf_eq, Set.mem_insert_iff]














theorem arcns_arc_no_separation {u w : Site 2} (p : (hypercubicLattice 2).Walk u w)
    (hp : p.IsPath)
    (hleaf : ∀ (a b c : Site 2) (h : (hypercubicLattice 2).Adj a b)
      (q : (hypercubicLattice 2).Walk b c), (Walk.cons h q).IsPath →
        arcns_LeafRemovable {z : Site 2 | z ∈ q.support} a) :
    arcns_OffSupportConnected {z : Site 2 | z ∈ p.support} := by
  induction p with
  | nil =>
    
    rename_i v
    have hsupp : {z : Site 2 | z ∈ (Walk.nil : (hypercubicLattice 2).Walk v v).support}
        = ({v} : Set (Site 2)) := by
      ext z; simp [Walk.support_nil]
    rw [hsupp]; exact arcns_singlePoint_connected v
  | @cons a b c h q ih =>
    have hpath : (Walk.cons h q).IsPath := hp
    have hqpath : q.IsPath := hpath.of_cons
    have hIH : arcns_OffSupportConnected {z : Site 2 | z ∈ q.support} := ih hqpath
    rw [arcns_cons_support]
    exact arcns_connected_insert_of_leafRemovable (hleaf a b c h q hpath) hIH













theorem arcns_offSupport_reachable_of_arc {u w : Site 2} (p : (hypercubicLattice 2).Walk u w)
    (hp : p.IsPath)
    (hleaf : ∀ (a b c : Site 2) (h : (hypercubicLattice 2).Adj a b)
      (q : (hypercubicLattice 2).Walk b c), (Walk.cons h q).IsPath →
        arcns_LeafRemovable {z : Site 2 | z ∈ q.support} a)
    {x y : Site 2} (hx : x ∉ {z : Site 2 | z ∈ p.support})
    (hy : y ∉ {z : Site 2 | z ∈ p.support}) :
    (ffc_offSupportLattice {z : Site 2 | z ∈ p.support}).Reachable x y :=
  arcns_arc_no_separation p hp hleaf x y hx hy





theorem arcns_floodFill_eq_offSupport_of_arc {u w : Site 2}
    (p : (hypercubicLattice 2).Walk u w) (hp : p.IsPath)
    (hleaf : ∀ (a b c : Site 2) (h : (hypercubicLattice 2).Adj a b)
      (q : (hypercubicLattice 2).Walk b c), (Walk.cons h q).IsPath →
        arcns_LeafRemovable {z : Site 2 | z ∈ q.support} a)
    {seed : Site 2} (hseed : seed ∉ {z : Site 2 | z ∈ p.support}) :
    ffc_floodFill {z : Site 2 | z ∈ p.support} seed
      = {z : Site 2 | z ∉ {z : Site 2 | z ∈ p.support}} := by
  ext z
  constructor
  · intro hz
    exact ffc_floodFill_offSupport hseed hz
  · intro hz
    rw [Set.mem_setOf_eq] at hz
    rw [ffc_mem_floodFill]
    exact arcns_arc_no_separation p hp hleaf seed z hseed hz













theorem arcns_singlePoint_nonvacuous :
    (ffc_offSupportLattice ({![0, 0]} : Set (Site 2))).Reachable ![1, 0] ![0, 1] := by
  apply arcns_singlePoint_connected
  · simp only [Set.mem_singleton_iff]; intro h; have := congrFun h 0; simp at this
  · simp only [Set.mem_singleton_iff]; intro h; have := congrFun h 1; simp at this







theorem arcns_leafRemovable_empty (u : Site 2) :
    arcns_LeafRemovable (∅ : Set (Site 2)) u := by
  intro _
  have hins : (insert u (∅ : Set (Site 2))) = ({u} : Set (Site 2)) := by simp
  rw [hins]; exact arcns_singlePoint_connected u


































end Lattice

end StatMech
