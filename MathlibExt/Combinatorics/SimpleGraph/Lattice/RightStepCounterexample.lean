/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.RightStep

/-!
# A closed walk for which the right-step property fails

Let `edc_ring` be the closed walk from `(1, 0)` around the eight neighbours of the origin in `ℤ²`
and `edc_Vc` that walk followed by its reverse. Every edge of `edc_Vc` is traversed twice, so every
ray count is even and every site, the origin included, is outside `edc_Vc`. The origin is off the
walk but its four lattice neighbours are on it, so the origin is isolated once the walk is removed.
Hence the right-step property `ecc_RightStep edc_Vc R` and the dodge property
`ecc_RightDodge edc_Vc R` fail for every `R`.

## Main definitions

* `StatMech.Lattice.edc_ring`: the closed walk around the eight neighbours of the origin.
* `StatMech.Lattice.edc_Vc`: `edc_ring` followed by its reverse.

## Main results

* `StatMech.Lattice.edc_isolated_reachable_eq`: the origin reaches only itself off `edc_Vc`.
* `StatMech.Lattice.edc_z_outside`: the origin is outside `edc_Vc`.
* `StatMech.Lattice.edc_rightStep_refuted`, `StatMech.Lattice.edc_rightDodge_refuted`: the
  right-step and dodge properties fail for `edc_Vc`.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- The closed walk `(1,0) → (1,1) → (0,1) → (-1,1) → (-1,0) → (-1,-1) → (0,-1) → (1,-1) → (1,0)`
around the eight neighbours of the origin. -/
noncomputable def edc_ring : (hypercubicLattice 2).Walk ![(1 : ℤ), 0] ![(1 : ℤ), 0] :=
  (Walk.cons (show (hypercubicLattice 2).Adj ![(1 : ℤ), 0] ![(1 : ℤ), 1] by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide)
  (Walk.cons (show (hypercubicLattice 2).Adj ![(1 : ℤ), 1] ![(0 : ℤ), 1] by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide)
  (Walk.cons (show (hypercubicLattice 2).Adj ![(0 : ℤ), 1] ![(-1 : ℤ), 1] by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide)
  (Walk.cons (show (hypercubicLattice 2).Adj ![(-1 : ℤ), 1] ![(-1 : ℤ), 0] by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide)
  (Walk.cons (show (hypercubicLattice 2).Adj ![(-1 : ℤ), 0] ![(-1 : ℤ), -1] by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide)
  (Walk.cons (show (hypercubicLattice 2).Adj ![(-1 : ℤ), -1] ![(0 : ℤ), -1] by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide)
  (Walk.cons (show (hypercubicLattice 2).Adj ![(0 : ℤ), -1] ![(1 : ℤ), -1] by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide)
  (Walk.cons (show (hypercubicLattice 2).Adj ![(1 : ℤ), -1] ![(1 : ℤ), 0] by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide)
  Walk.nil))))))))

/-- The closed walk `edc_ring` followed by its reverse; each edge is traversed twice. -/
noncomputable def edc_Vc : (hypercubicLattice 2).Walk ![(1 : ℤ), 0] ![(1 : ℤ), 0] :=
  edc_ring.append edc_ring.reverse

theorem edc_mem_support_iff (w : Site 2) : w ∈ edc_Vc.support ↔ w ∈ edc_ring.support := by
  unfold edc_Vc
  rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse, or_self]

theorem edc_z_offSupport : (![(0 : ℤ), 0] : Site 2) ∉ edc_Vc.support := by
  rw [edc_mem_support_iff]
  unfold edc_ring
  simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false]
  decide

theorem edc_neighbours_onSupport :
    (![(1 : ℤ), 0] : Site 2) ∈ edc_Vc.support ∧ (![(-1 : ℤ), 0] : Site 2) ∈ edc_Vc.support ∧
      (![(0 : ℤ), 1] : Site 2) ∈ edc_Vc.support ∧ (![(0 : ℤ), -1] : Site 2) ∈ edc_Vc.support := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [edc_mem_support_iff]
    unfold edc_ring
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false]
    decide

theorem edc_adj_centre_cases {y : Site 2}
    (h : (hypercubicLattice 2).Adj (![(0 : ℤ), 0] : Site 2) y) :
    y = ![1, 0] ∨ y = ![-1, 0] ∨ y = ![0, 1] ∨ y = ![0, -1] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  have hy : y = ![y 0, y 1] := by ext i; fin_cases i <;> simp
  have key : y 0 = 1 ∧ y 1 = 0 ∨ y 0 = -1 ∧ y 1 = 0 ∨ y 0 = 0 ∧ y 1 = 1 ∨ y 0 = 0 ∧ y 1 = -1 := by
    omega
  rw [hy]
  rcases key with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> simp only [a, b] <;> tauto

theorem edc_z_isolated (y : Site 2) : ¬ (offSupport edc_Vc).Adj (![(0 : ℤ), 0] : Site 2) y := by
  rintro ⟨hadj, _, hyoff⟩
  obtain ⟨h1, h2, h3, h4⟩ := edc_neighbours_onSupport
  rcases edc_adj_centre_cases hadj with rfl | rfl | rfl | rfl
  · exact hyoff h1
  · exact hyoff h2
  · exact hyoff h3
  · exact hyoff h4

theorem edc_isolated_walk_eq {w : Site 2}
    (p : (offSupport edc_Vc).Walk (![(0 : ℤ), 0] : Site 2) w) : w = ![0, 0] := by
  cases p with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (edc_z_isolated _)

/-- Off `edc_Vc`, the origin reaches only itself: its four neighbours are on the walk. -/
theorem edc_isolated_reachable_eq {w : Site 2}
    (h : (offSupport edc_Vc).Reachable (![(0 : ℤ), 0] : Site 2) w) : w = ![0, 0] := by
  obtain ⟨p⟩ := h
  exact edc_isolated_walk_eq p

theorem edc_rayCount_even (z : Site 2) : Even (jec_rayCount z edc_Vc) := by
  unfold edc_Vc
  rw [jec_rayCount_append, jec_rayCount_reverse]
  exact ⟨_, rfl⟩

/-- The origin is outside `edc_Vc`: every ray count of a walk followed by its reverse is even. -/
theorem edc_z_outside : (![(0 : ℤ), 0] : Site 2) ∉ jec_leftRegion edc_Vc := by
  rw [jec_mem_leftRegion, not_not]; exact edc_rayCount_even _

/-- The right-step property fails for `edc_Vc`, for every `R`. -/
theorem edc_rightStep_refuted (R : ℕ) : ¬ ecc_RightStep edc_Vc R := by
  intro hstep
  obtain ⟨w, hprog, hreach⟩ :=
    hstep ![0, 0] edc_z_outside edc_z_offSupport (by simp)
  have hw : w = ![0, 0] := edc_isolated_reachable_eq hreach
  rw [hw] at hprog
  simp at hprog

/-- The dodge property fails for `edc_Vc`, for every `R`. -/
theorem edc_rightDodge_refuted (R : ℕ) : ¬ ecc_RightDodge edc_Vc R := by
  intro hdodge
  have hnb : (![(0 : ℤ) + 1, 0] : Site 2) ∈ edc_Vc.support := by
    have h1 := edc_neighbours_onSupport.1
    simp only [show (0 : ℤ) + 1 = 1 from rfl]; exact h1
  obtain ⟨w, hprog, hreach⟩ :=
    hdodge ![0, 0] edc_z_outside edc_z_offSupport (by simp) hnb
  have hw : w = ![0, 0] := edc_isolated_reachable_eq hreach
  rw [hw] at hprog
  simp at hprog

theorem edc_centre_reaches_only_self {w : Site 2}
    (h : (offSupport edc_Vc).Reachable (![(0 : ℤ), 0] : Site 2) w) : w 0 = 0 ∧ w 1 = 0 := by
  have hw : w = ![0, 0] := edc_isolated_reachable_eq h
  rw [hw]; exact ⟨by simp, by simp⟩

end Lattice

end StatMech
