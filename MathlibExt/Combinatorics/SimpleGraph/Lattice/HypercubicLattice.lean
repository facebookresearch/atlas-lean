/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Int.Interval
import Mathlib.Algebra.CharP.Defs
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.Ring.RingNF

/-!
# The hypercubic lattice `ℤ^d`

This file defines the nearest-neighbour graph on `ℤ^d`, the boxes `[-n, n]^d`, and the vertex and
edge boundaries used throughout the lattice percolation and Ising developments.

## Main definitions

* `StatMech.Lattice.Site d`: a site of `ℤ^d`, encoded as `Fin d → ℤ`.
* `StatMech.Lattice.hypercubicLattice d`: the simple graph on `ℤ^d` joining sites at `ℓ¹`-distance
  one.
* `StatMech.Lattice.box d n`: the box `[-n, n]^d`.
* `StatMech.Lattice.vertexBoundary d n`, `StatMech.Lattice.edgeBoundary d S`: the sites of `box d n`
  outside `box d (n - 1)`, and the nearest-neighbour pairs with exactly one endpoint in `S`.

## Main results

* `StatMech.Lattice.box_finite`: boxes are finite.
* `StatMech.Lattice.iUnion_box`: the boxes exhaust `ℤ^d`.
* `StatMech.Lattice.finite_subset_box`: every finite set of sites lies in a box.
* `StatMech.Lattice.hypercubicLattice_two_reachable`: the square lattice `ℤ²` is connected.

See also `Crystal.hypercubicGraph` in PhyslibAlpha, which builds the same graph as a periodic
crystal graph; `MathlibExt` cannot import it, so no bridge is stated here.
-/

@[expose] public section

open Set Finset

namespace StatMech

namespace Lattice

/-- A site of the `d`-dimensional hypercubic lattice `ℤ^d`, encoded as an integer vector. -/
abbrev Site (d : ℕ) : Type := Fin d → ℤ

/-- Two sites are nearest neighbours when their `ℓ¹` distance `∑ i, |x i - y i|` equals one. -/
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

/-- The hypercubic lattice `ℤ^d`: the simple graph on `Site d` whose edges join
nearest
neighbours. -/
def hypercubicLattice (d : ℕ) : SimpleGraph (Site d) where
  Adj := NearestNeighbour d
  symm := ⟨fun _ _ h => nearestNeighbour_symm d h⟩
  loopless := nearestNeighbour_irrefl d

@[simp]
theorem hypercubicLattice_adj (d : ℕ) (x y : Site d) :
    (hypercubicLattice d).Adj x y ↔ (∑ i, (x i - y i).natAbs) = 1 := Iff.rfl

/-- The box `[-n, n]^d` of sites whose coordinates all have absolute value at most `n`. -/
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

/-- The inner vertex boundary of `box d n`: sites of `box d n` that are not in `box d (n - 1)`. -/
def vertexBoundary (d n : ℕ) : Set (Site d) := box d n \ box d (n - 1)

@[simp]
theorem mem_vertexBoundary {d n : ℕ} {x : Site d} :
    x ∈ vertexBoundary d n ↔ x ∈ box d n ∧ x ∉ box d (n - 1) := Iff.rfl

theorem vertexBoundary_finite (d n : ℕ) : (vertexBoundary d n).Finite :=
  (box_finite d n).subset (Set.sdiff_subset)

/-- The edge boundary of a set `S` of sites: ordered nearest-neighbour pairs with exactly one
endpoint in `S`. -/
def edgeBoundary (d : ℕ) (S : Set (Site d)) : Set (Site d × Site d) :=
  {p | (hypercubicLattice d).Adj p.1 p.2 ∧ (p.1 ∈ S ↔ p.2 ∉ S)}

@[simp]
theorem mem_edgeBoundary {d : ℕ} {S : Set (Site d)} {x y : Site d} :
    (x, y) ∈ edgeBoundary d S ↔ (hypercubicLattice d).Adj x y ∧ (x ∈ S ↔ y ∉ S) :=
  Iff.rfl

theorem edgeBoundary_symm {d : ℕ} {S : Set (Site d)} {x y : Site d}
    (h : (x, y) ∈ edgeBoundary d S) : (y, x) ∈ edgeBoundary d S := by
  obtain ⟨hadj, hxy⟩ := h
  refine ⟨hadj.symm, ?_⟩
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

/-- Every finite set of sites lies in some box `box d R`. -/
theorem finite_subset_box {d : ℕ} (F : Set (Site d)) (hF : F.Finite) : ∃ R : ℕ, F ⊆ box d R := by
  classical
  set g : Site d → ℕ := fun x => Finset.univ.sup (fun i => (x i).natAbs) with hg
  refine ⟨hF.toFinset.sup g, ?_⟩
  intro x hx i
  have hxF : x ∈ hF.toFinset := by rwa [Set.Finite.mem_toFinset]
  have h1 : (x i).natAbs ≤ g x := Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ i)
  have h2 : g x ≤ hF.toFinset.sup g := Finset.le_sup hxF
  exact h1.trans h2

/-- In `ℤ²`, increasing one coordinate by `n` stays in the same component. -/
theorem reachable_update_add (x : Site 2) (j : Fin 2) (a : ℤ) (n : ℕ) :
    (hypercubicLattice 2).Reachable (Function.update x j a) (Function.update x j (a + n)) := by
  induction n with
  | zero => simp
  | succ m ih =>
    refine ih.trans (SimpleGraph.Adj.reachable ?_)
    rw [hypercubicLattice_adj, Finset.sum_eq_single j]
    · simp only [Function.update_self]
      have : a + ((m : ℕ) : ℤ) - (a + ((m + 1 : ℕ) : ℤ)) = -1 := by push_cast; ring
      rw [this]; rfl
    · intro b _ hb; rw [Function.update_of_ne hb, Function.update_of_ne hb]; simp
    · intro h; exact absurd (Finset.mem_univ j) h

/-- In `ℤ²`, changing one coordinate stays in the same component. -/
theorem reachable_update (x : Site 2) (j : Fin 2) (a b : ℤ) :
    (hypercubicLattice 2).Reachable (Function.update x j a) (Function.update x j b) := by
  rcases le_total a b with hab | hab
  · obtain ⟨n, rfl⟩ := Int.le.dest hab; exact reachable_update_add x j a n
  · obtain ⟨n, rfl⟩ := Int.le.dest hab; exact (reachable_update_add x j b n).symm

/-- The square lattice `ℤ²` is connected. -/
theorem hypercubicLattice_two_reachable (x y : Site 2) : (hypercubicLattice 2).Reachable x y := by
  have h1 : (hypercubicLattice 2).Reachable x (Function.update x 0 (y 0)) := by
    have := reachable_update x 0 (x 0) (y 0); rwa [Function.update_eq_self] at this
  set z := Function.update x 0 (y 0) with hz
  have h2 : (hypercubicLattice 2).Reachable z (Function.update z 1 (y 1)) := by
    have := reachable_update z 1 (z 1) (y 1); rwa [Function.update_eq_self] at this
  have hzy : Function.update z 1 (y 1) = y := by funext i; fin_cases i <;> simp [hz]
  rw [hzy] at h2; exact h1.trans h2

end Lattice

end StatMech
