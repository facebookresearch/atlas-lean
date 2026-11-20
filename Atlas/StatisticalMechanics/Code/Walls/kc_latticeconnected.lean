/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.SegmentConn

open Set SimpleGraph

namespace StatMech

namespace Walls

open StatMech.Lattice

variable {d : ℕ}












theorem kc_reach_axis_le (x : Site d) (j : Fin d) (a : ℤ) (n : ℕ) :
    (hypercubicLattice d).Reachable (Function.update x j a)
      (Function.update x j (a + (n : ℤ))) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have step : (hypercubicLattice d).Adj (Function.update x j (a + (m : ℤ)))
        (Function.update x j (a + (m : ℤ) + 1)) := adj_update_succ x j (a + (m : ℤ))
    refine ih.trans (SimpleGraph.Adj.reachable ?_)
    have he : a + (((m : ℕ) + 1 : ℕ) : ℤ) = a + (m : ℤ) + 1 := by push_cast; ring
    rw [he]; exact step




theorem kc_reach_axis (x : Site d) (j : Fin d) (a b : ℤ) :
    (hypercubicLattice d).Reachable (Function.update x j a) (Function.update x j b) := by
  rcases le_total a b with hab | hab
  · obtain ⟨n, rfl⟩ := Int.le.dest hab; exact kc_reach_axis_le x j a n
  · obtain ⟨n, rfl⟩ := Int.le.dest hab; exact (kc_reach_axis_le x j b n).symm










private def kc_merge (x y : Site d) (k : ℕ) : Site d :=
  fun i => if (i : ℕ) < k then y i else x i

private theorem kc_merge_zero (x y : Site d) : kc_merge x y 0 = x := by
  funext i; simp [kc_merge]

private theorem kc_merge_full (x y : Site d) : kc_merge x y d = y := by
  funext i; simp only [kc_merge, i.isLt, if_pos]



private theorem kc_merge_update (x y : Site d) (k : ℕ) (hk : k < d) :
    Function.update (kc_merge x y k) ⟨k, hk⟩ (y ⟨k, hk⟩) = kc_merge x y (k + 1) := by
  funext i
  by_cases hik : i = ⟨k, hk⟩
  · subst hik; simp [kc_merge]
  · rw [Function.update_of_ne hik]
    have hne : (i : ℕ) ≠ k := fun h => hik (Fin.ext h)
    simp only [kc_merge]
    by_cases hlt : (i : ℕ) < k
    · rw [if_pos hlt, if_pos (Nat.lt_succ_of_lt hlt)]
    · rw [if_neg hlt, if_neg (by omega)]




private theorem kc_reach_merge (x y : Site d) : ∀ k ≤ d,
    (hypercubicLattice d).Reachable x (kc_merge x y k) := by
  intro k
  induction k with
  | zero => intro _; rw [kc_merge_zero]
  | succ m ih =>
    intro hm
    have hmd : m < d := hm
    have hstep : (hypercubicLattice d).Reachable (kc_merge x y m) (kc_merge x y (m + 1)) := by
      have hseg := kc_reach_axis (kc_merge x y m) ⟨m, hmd⟩
        ((kc_merge x y m) ⟨m, hmd⟩) (y ⟨m, hmd⟩)
      rw [Function.update_eq_self] at hseg
      rwa [kc_merge_update x y m hmd] at hseg
    exact (ih (le_of_lt hmd)).trans hstep





theorem kc_reach_all_d (x y : Site d) : (hypercubicLattice d).Reachable x y := by
  have h := kc_reach_merge x y d le_rfl
  rwa [kc_merge_full] at h



theorem kc_lattice_preconnected : (hypercubicLattice d).Preconnected :=
  fun x y => kc_reach_all_d x y


theorem kc_lattice_connected : (hypercubicLattice d).Connected where
  preconnected := kc_lattice_preconnected
  nonempty := ⟨fun _ => 0⟩







theorem kc_reach_all (x y : Site 2) : (hypercubicLattice 2).Reachable x y :=
  kc_reach_all_d x y


theorem kc_lattice2_preconnected : (hypercubicLattice 2).Preconnected :=
  kc_lattice_preconnected


theorem kc_lattice2_connected : (hypercubicLattice 2).Connected :=
  kc_lattice_connected

end Walls

end StatMech
