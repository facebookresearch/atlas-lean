/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















































import Mathlib
import Code.Onsager.WindingBridge
import Code.Lattice.CrossingParity

namespace StatMech.Onsager.InteriorRegion

open StatMech.Lattice
open StatMech.Onsager.ChordCut
open StatMech.Onsager.InteriorReaches
open StatMech.Onsager.WindingBridge




def liftS (P : Finset Pt) : Set (Site 2) := toSite '' (P : Set Pt)


theorem liftS_finite (P : Finset Pt) : (liftS P).Finite :=
  P.finite_toSet.image _



theorem mem_liftS (P : Finset Pt) (q : Pt) : toSite q ∈ liftS P ↔ q ∈ P := by
  constructor
  · rintro ⟨r, hr, hEq⟩
    rw [← toSite_injective hEq]
    exact hr
  · intro h
    exact ⟨q, h, rfl⟩






noncomputable def Lcells : Finset Pt :=
  ((Finset.Icc (0 : ℤ) 3) ×ˢ (Finset.Icc (0 : ℤ) 3)).filter (fun q => ¬ (q.1 ≤ 1 ∧ q.2 ≤ 1))


theorem mem_Lcells (q : Pt) :
    q ∈ Lcells ↔ (0 ≤ q.1 ∧ q.1 ≤ 3 ∧ 0 ≤ q.2 ∧ q.2 ≤ 3) ∧ ¬ (q.1 ≤ 1 ∧ q.2 ≤ 1) := by
  simp only [Lcells, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  tauto


def Lint : Set (Site 2) := liftS Lcells


theorem Lint_finite : Lint.Finite := liftS_finite Lcells




def wReflex : Pt := (1, 1)


theorem wReflex_not_interior : toSite wReflex ∉ Lint := by
  rw [Lint, mem_liftS, mem_Lcells]
  simp only [wReflex]
  omega


theorem launch_pt_interior : toSite (wReflex.1 + 1, wReflex.2) ∈ Lint := by
  rw [Lint, mem_liftS, mem_Lcells]
  simp only [wReflex]
  omega



theorem launch_interior : toSite (rayX wReflex 1) ∈ Lint := by
  have : rayX wReflex 1 = (wReflex.1 + 1, wReflex.2) := by
    simp only [rayX, wReflex]; norm_num
  rw [this]; exact launch_pt_interior




theorem wReflex_mem_boundary : wReflex ∈ (mkBoxData Lint Lint_finite).B := by
  rw [mkBoxData, Set.Finite.mem_toFinset, Bset, Set.mem_setOf_eq, bdEdge_mk]
  constructor
  · intro h; exact absurd h wReflex_not_interior
  · intro h; exact absurd launch_pt_interior h








theorem wReflex_isReflex :
    cross (1, 0) (0, -1) = -1 ∧
      (cross (1, 0) (1, 0) = 0 ∧ 0 < cross (0, -1) (1, 0)) := by
  refine ⟨by decide, ?_⟩
  exact reflex_continuation_interior (1, 0) (0, -1) (Or.inl rfl) (by decide)




theorem wReflex_quadrant :
    (toSite (2, 1) ∈ Lint ∧ toSite (1, 2) ∈ Lint) ∧
      (toSite (0, 1) ∉ Lint ∧ toSite (1, 0) ∉ Lint) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
    · rw [Lint, mem_liftS, mem_Lcells]; simp only; omega







theorem Lshape_interiorReaches :
    InteriorReaches (mkBoxData Lint Lint_finite) wReflex :=
  interiorReaches_of_cluster Lint Lint_finite wReflex launch_interior






theorem Lshape_chord :
    ∃ k : ℕ, 1 ≤ k ∧ rayX wReflex k ∈ (mkBoxData Lint Lint_finite).B ∧
      (∀ j : ℕ, 1 ≤ j → j < k → rayX wReflex j ∉ (mkBoxData Lint Lint_finite).B) :=
  chord_of_cluster Lint Lint_finite wReflex wReflex_mem_boundary launch_interior











def rayWalk (p : Pt) : (N : ℕ) → (hypercubicLattice 2).Walk (toSite p) (toSite (rayX p N))
  | 0 => SimpleGraph.Walk.nil.copy rfl (by simp [rayX])
  | (N + 1) => by
      have adj : (hypercubicLattice 2).Adj (toSite (rayX p N)) (toSite (rayX p (N + 1))) := by
        have h := toSite_adj_shift (rayX p N)
        rwa [shift_ray p N] at h
      exact (rayWalk p N).concat adj






theorem interior_iff_odd_crossing (S : Set (Site 2)) (p : Pt) (N : ℕ)
    (hout : toSite (rayX p N) ∉ S) :
    toSite p ∈ S ↔ ¬ Even (crossCount S (rayWalk p N)) := by
  have h := crossCount_parity S (rayWalk p N)
  constructor
  · intro hp hev
    exact hout ((h.mp hev).mp hp)
  · intro hne
    by_contra hp
    apply hne
    rw [h]
    constructor
    · intro hp'; exact absurd hp' hp
    · intro hz; exact absurd hz hout









































end StatMech.Onsager.InteriorRegion
