/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Mathlib

open Set Finset

namespace StatMech

namespace Lattice


abbrev Site (d : ℕ) : Type := Fin d → ℤ




def NearestNeighbour (d : ℕ) (x y : Site d) : Prop :=
  (∑ i, (x i - y i).natAbs) = 1

theorem nearestNeighbour_symm (d : ℕ) : Symmetric (NearestNeighbour d) := by
  intro x y h
  change (∑ i, (y i - x i).natAbs) = 1
  rw [← h]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Int.natAbs_neg, neg_sub]

theorem nearestNeighbour_irrefl (d : ℕ) : Std.Irrefl (NearestNeighbour d) := by
  refine ⟨fun x h => ?_⟩
  simp only [NearestNeighbour, sub_self, Int.natAbs_zero, Finset.sum_const_zero] at h
  exact absurd h (by norm_num)



def hypercubicLattice (d : ℕ) : SimpleGraph (Site d) where
  Adj := NearestNeighbour d
  symm := nearestNeighbour_symm d
  loopless := nearestNeighbour_irrefl d

@[simp]
theorem hypercubicLattice_adj (d : ℕ) (x y : Site d) :
    (hypercubicLattice d).Adj x y ↔ (∑ i, (x i - y i).natAbs) = 1 := Iff.rfl



def box (d n : ℕ) : Set (Site d) := {x | ∀ i, (x i).natAbs ≤ n}

@[simp]
theorem mem_box {d n : ℕ} {x : Site d} : x ∈ box d n ↔ ∀ i, (x i).natAbs ≤ n := Iff.rfl


theorem box_finite (d n : ℕ) : (box d n).Finite := by
  apply Set.Finite.subset
    (Set.Finite.pi (fun _ : Fin d => Set.finite_Icc (-(n : ℤ)) (n : ℤ)))
  intro x hx i _
  rw [Set.mem_Icc]
  have hx' : (x i).natAbs ≤ n := hx i
  have habs : |x i| ≤ (n : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hx'
  exact abs_le.mp habs


def vertexBoundary (d n : ℕ) : Set (Site d) := box d n \ box d (n - 1)

@[simp]
theorem mem_vertexBoundary {d n : ℕ} {x : Site d} :
    x ∈ vertexBoundary d n ↔ x ∈ box d n ∧ x ∉ box d (n - 1) := Iff.rfl

theorem vertexBoundary_finite (d n : ℕ) : (vertexBoundary d n).Finite :=
  (box_finite d n).subset (Set.diff_subset)



def edgeBoundary (d : ℕ) (S : Set (Site d)) : Set (Site d × Site d) :=
  {p | (hypercubicLattice d).Adj p.1 p.2 ∧ (p.1 ∈ S ↔ p.2 ∉ S)}

@[simp]
theorem mem_edgeBoundary {d : ℕ} {S : Set (Site d)} {x y : Site d} :
    (x, y) ∈ edgeBoundary d S ↔ (hypercubicLattice d).Adj x y ∧ (x ∈ S ↔ y ∉ S) :=
  Iff.rfl


theorem edgeBoundary_symm {d : ℕ} {S : Set (Site d)} {x y : Site d}
    (h : (x, y) ∈ edgeBoundary d S) : (y, x) ∈ edgeBoundary d S := by
  obtain ⟨hadj, hxy⟩ := h
  refine ⟨(hypercubicLattice d).symm hadj, ?_⟩
  classical
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;> tauto




theorem box_mono (d : ℕ) : Monotone (box d) := by
  intro m n hmn x hx i
  exact le_trans (hx i) hmn

theorem box_subset_succ (d n : ℕ) : box d n ⊆ box d (n + 1) :=
  box_mono d (Nat.le_succ n)


theorem iUnion_box (d : ℕ) : (⋃ n, box d n) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  rw [Set.mem_iUnion]
  refine ⟨Finset.univ.sup (fun i => (x i).natAbs), fun i => ?_⟩
  exact Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ i)

end Lattice

end StatMech
