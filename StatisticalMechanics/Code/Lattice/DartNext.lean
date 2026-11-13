/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.DartDef

open SimpleGraph

namespace StatMech

namespace Lattice











def unitWt (z : Site 2) : ℕ := ∑ i, (z i).natAbs



theorem adj_iff_unitWt_sub (x y : Site 2) :
    (hypercubicLattice 2).Adj x y ↔ unitWt (x - y) = 1 := by
  simp only [hypercubicLattice_adj, unitWt]
  refine Iff.of_eq (congrArg (· = 1) ?_)
  apply Finset.sum_congr rfl
  intro i _
  rw [Pi.sub_apply]


theorem unitWt_neg (z : Site 2) : unitWt (-z) = unitWt z := by
  unfold unitWt
  apply Finset.sum_congr rfl
  intro i _
  rw [Pi.neg_apply, Int.natAbs_neg]



theorem unitWt_rot90Fun (z : Site 2) : unitWt (rot90Fun z) = unitWt z := by
  unfold unitWt rot90Fun
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Int.natAbs_neg]
  ring


theorem unitWt_dir (e : Dart) : unitWt e.dir = 1 := by
  have h := e.adj
  rw [adj_iff_unitWt_sub] at h
  rw [Dart.dir_def, ← unitWt_neg, neg_sub]
  exact h



theorem unitWt_rot90Fun_dir (e : Dart) : unitWt (rot90Fun e.dir) = 1 := by
  rw [unitWt_rot90Fun]; exact unitWt_dir e



theorem unitWt_neg_rot90Fun_dir (e : Dart) : unitWt (-rot90Fun e.dir) = 1 := by
  rw [unitWt_neg]; exact unitWt_rot90Fun_dir e





def mkDart (p g : Site 2) (hg : unitWt g = 1) : Dart where
  tail := p
  head := p + g
  adj := by
    rw [adj_iff_unitWt_sub, show p - (p + g) = -g by abel, unitWt_neg]
    exact hg

@[simp] theorem mkDart_tail (p g : Site 2) (hg : unitWt g = 1) :
    (mkDart p g hg).tail = p := rfl

@[simp] theorem mkDart_head (p g : Site 2) (hg : unitWt g = 1) :
    (mkDart p g hg).head = p + g := rfl

@[simp] theorem mkDart_dir (p g : Site 2) (hg : unitWt g = 1) :
    (mkDart p g hg).dir = g := by
  rw [Dart.dir_def, mkDart_head, mkDart_tail]; abel





def IsBoundaryDart (K : Set (Site 2)) (e : Dart) : Prop :=
  e.tail ∈ K ∧ e.head ∉ K

theorem IsBoundaryDart.tail_mem {K : Set (Site 2)} {e : Dart}
    (h : IsBoundaryDart K e) : e.tail ∈ K := h.1

theorem IsBoundaryDart.head_not_mem {K : Set (Site 2)} {e : Dart}
    (h : IsBoundaryDart K e) : e.head ∉ K := h.2













noncomputable def dartNext (K : Set (Site 2)) (e : Dart) : Dart := by
  classical
  exact
    if e.head + (-rot90Fun e.dir) ∈ K then
      mkDart (e.head + (-rot90Fun e.dir)) (rot90Fun e.dir) (unitWt_rot90Fun_dir e)
    else if e.tail + (-rot90Fun e.dir) ∈ K then
      mkDart (e.tail + (-rot90Fun e.dir)) e.dir (unitWt_dir e)
    else
      mkDart e.tail (-rot90Fun e.dir) (unitWt_neg_rot90Fun_dir e)





theorem dartNext_of_front_mem (K : Set (Site 2)) (e : Dart)
    (h : e.head + (-rot90Fun e.dir) ∈ K) :
    dartNext K e = mkDart (e.head + (-rot90Fun e.dir)) (rot90Fun e.dir)
      (unitWt_rot90Fun_dir e) := by
  classical
  unfold dartNext; rw [if_pos h]



theorem dartNext_front_head (K : Set (Site 2)) (e : Dart)
    (h : e.head + (-rot90Fun e.dir) ∈ K) :
    (dartNext K e).head = e.head ∧ (dartNext K e).dir = rot90Fun e.dir := by
  classical
  refine ⟨?_, ?_⟩
  · rw [dartNext_of_front_mem K e h, mkDart_head]; abel
  · rw [dartNext_of_front_mem K e h, mkDart_dir]



theorem dartNext_of_side_mem (K : Set (Site 2)) (e : Dart)
    (h1 : e.head + (-rot90Fun e.dir) ∉ K) (h2 : e.tail + (-rot90Fun e.dir) ∈ K) :
    dartNext K e = mkDart (e.tail + (-rot90Fun e.dir)) e.dir (unitWt_dir e) := by
  classical
  unfold dartNext; rw [if_neg h1, if_pos h2]



theorem dartNext_of_corner (K : Set (Site 2)) (e : Dart)
    (h1 : e.head + (-rot90Fun e.dir) ∉ K) (h2 : e.tail + (-rot90Fun e.dir) ∉ K) :
    dartNext K e = mkDart e.tail (-rot90Fun e.dir) (unitWt_neg_rot90Fun_dir e) := by
  classical
  unfold dartNext; rw [if_neg h1, if_neg h2]



















theorem dartNext_isBoundaryDart (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) : IsBoundaryDart K (dartNext K e) := by
  classical
  obtain ⟨hc, hv⟩ := he
  unfold dartNext IsBoundaryDart
  split_ifs with h1 h2
  · 
    refine ⟨by simpa using h1, ?_⟩
    rw [mkDart_head]
    have : e.head + -rot90Fun e.dir + rot90Fun e.dir = e.head := by abel
    rw [this]; exact hv
  · 
    refine ⟨by simpa using h2, ?_⟩
    rw [mkDart_head]
    have : e.tail + -rot90Fun e.dir + e.dir = e.head + -rot90Fun e.dir := by
      rw [Dart.dir_def]; abel
    rw [this]; exact h1
  · 
    exact ⟨by simpa using hc, by simpa using h2⟩

end Lattice

end StatMech
