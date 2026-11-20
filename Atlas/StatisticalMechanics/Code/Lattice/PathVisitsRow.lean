/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























import Mathlib
import Code.Lattice.HypercubicLattice

open Set Finset SimpleGraph

namespace StatMech

namespace Lattice







theorem pvr_adj_coord_diff_le_one {d : ℕ} {x y : Site d}
    (h : (hypercubicLattice d).Adj x y) (i : Fin d) :
    (x i - y i).natAbs ≤ 1 := by
  rw [hypercubicLattice_adj] at h
  calc (x i - y i).natAbs
      ≤ ∑ j, (x j - y j).natAbs :=
        Finset.single_le_sum (f := fun j => (x j - y j).natAbs)
          (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    _ = 1 := h












theorem pvr_discrete_ivt (f : ℕ → ℤ) :
    ∀ (n : ℕ), (∀ i, i < n → (f (i + 1) - f i).natAbs ≤ 1) →
      ∀ r, f 0 ≤ r → r ≤ f n → ∃ i ≤ n, f i = r := by
  intro n
  induction n with
  | zero =>
    intro _ r h0 hn
    exact ⟨0, le_refl 0, le_antisymm h0 hn⟩
  | succ m ih =>
    intro hstep r h0 hn
    have hm : (f (m + 1) - f m).natAbs ≤ 1 := hstep m (Nat.lt_succ_self m)
    by_cases hr : r ≤ f m
    · obtain ⟨i, hi, hfi⟩ := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi)) r h0 hr
      exact ⟨i, Nat.le_succ_of_le hi, hfi⟩
    · simp only [not_le] at hr
      refine ⟨m + 1, le_refl _, ?_⟩
      omega










theorem pvr_exists_idx_at_coord {a b : Site 2} (w : (hypercubicLattice 2).Walk a b)
    (k : Fin 2) {c d : ℤ} (hac : a k = c) (hbd : b k = d) (hcd : c ≤ d)
    (r : ℤ) (hr1 : c ≤ r) (hr2 : r ≤ d) :
    ∃ i ≤ w.length, (w.getVert i) k = r := by
  set f : ℕ → ℤ := fun i => (w.getVert i) k with hf
  have hf0 : f 0 = c := by simp only [hf, w.getVert_zero, hac]
  have hflen : f w.length = d := by simp only [hf, w.getVert_length, hbd]
  have hstep : ∀ i, i < w.length → (f (i + 1) - f i).natAbs ≤ 1 := by
    intro i hi
    have hadj := w.adj_getVert_succ hi
    have := pvr_adj_coord_diff_le_one hadj k
    simp only [hf]
    omega
  have h0 : f 0 ≤ r := by rw [hf0]; exact hr1
  have hn : r ≤ f w.length := by rw [hflen]; exact hr2
  
  have : c ≤ d := hcd
  exact pvr_discrete_ivt f w.length hstep r h0 hn




theorem pvr_visits_every_coord {a b : Site 2} (w : (hypercubicLattice 2).Walk a b)
    (k : Fin 2) {c d : ℤ} (hac : a k = c) (hbd : b k = d) (hcd : c ≤ d)
    (r : ℤ) (hr1 : c ≤ r) (hr2 : r ≤ d) :
    ∃ p ∈ w.support, p k = r := by
  obtain ⟨i, _, hfi⟩ := pvr_exists_idx_at_coord w k hac hbd hcd r hr1 hr2
  exact ⟨w.getVert i, w.getVert_mem_support i, hfi⟩






theorem pvr_visits_every_row {a b : Site 2} (w : (hypercubicLattice 2).Walk a b)
    {c d : ℤ} (hac : a 1 = c) (hbd : b 1 = d) (hcd : c ≤ d)
    (r : ℤ) (hr1 : c ≤ r) (hr2 : r ≤ d) :
    ∃ p ∈ w.support, p 1 = r :=
  pvr_visits_every_coord w 1 hac hbd hcd r hr1 hr2








theorem pvr_visits_every_col {a b : Site 2} (w : (hypercubicLattice 2).Walk a b)
    {c d : ℤ} (hac : a 0 = c) (hbd : b 0 = d) (hcd : c ≤ d)
    (r : ℤ) (hr1 : c ≤ r) (hr2 : r ≤ d) :
    ∃ p ∈ w.support, p 0 = r :=
  pvr_visits_every_coord w 0 hac hbd hcd r hr1 hr2





noncomputable def pvr_firstIdxAtCoord {a b : Site 2} (w : (hypercubicLattice 2).Walk a b)
    (k : Fin 2) (r : ℤ) (h : ∃ i, (w.getVert i) k = r) : ℕ :=
  Nat.find h


theorem pvr_firstIdxAtCoord_spec {a b : Site 2} (w : (hypercubicLattice 2).Walk a b)
    (k : Fin 2) (r : ℤ) (h : ∃ i, (w.getVert i) k = r) :
    (w.getVert (pvr_firstIdxAtCoord w k r h)) k = r :=
  Nat.find_spec h


theorem pvr_firstIdxAtCoord_min {a b : Site 2} (w : (hypercubicLattice 2).Walk a b)
    (k : Fin 2) (r : ℤ) (h : ∃ i, (w.getVert i) k = r) {j : ℕ}
    (hj : j < pvr_firstIdxAtCoord w k r h) :
    (w.getVert j) k ≠ r :=
  Nat.find_min h hj









theorem pvr_firstAtRow {a b : Site 2} (w : (hypercubicLattice 2).Walk a b)
    {c d : ℤ} (hac : a 1 = c) (hbd : b 1 = d) (hcd : c ≤ d)
    (r : ℤ) (hr1 : c ≤ r) (hr2 : r ≤ d) :
    ∃ i, (w.getVert i) 1 = r ∧ (∀ j, j < i → (w.getVert j) 1 ≠ r) := by
  have hex : ∃ i, (w.getVert i) 1 = r := by
    obtain ⟨i, _, hfi⟩ := pvr_exists_idx_at_coord w 1 hac hbd hcd r hr1 hr2
    exact ⟨i, hfi⟩
  refine ⟨pvr_firstIdxAtCoord w 1 r hex, pvr_firstIdxAtCoord_spec w 1 r hex, ?_⟩
  intro j hj
  exact pvr_firstIdxAtCoord_min w 1 r hex hj

end Lattice

end StatMech
