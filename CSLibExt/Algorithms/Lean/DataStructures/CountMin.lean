/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Count-Min sketch: deterministic guarantees

A Count-Min sketch keeps, for each of `d` hash functions, a row of counters; the estimate
for `x` is the minimum counter among the buckets `x` hashes to. This module follows the
construction of Cormode and Muthukrishnan for nonnegative item frequencies `f`: row `j`
uses an arbitrary hash `H j`, and its bucket `b` holds the total frequency of the items that
`H j` sends to `b` (`counter`). It proves the deterministic facts behind the point-query
estimate (`estimate`): the estimate never undercounts, it is at most every individual
counter, and a counter exceeds `f x` only by colliding mass. The probabilistic `(ε, δ)`
bound on the overcount is not proved here.

## References

* G. Cormode and S. Muthukrishnan, *An improved data stream summary: the count-min sketch
  and its applications*, J. Algorithms 55 (2005), 58–75.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean

namespace CountMin

/-- Count-Min counter for hash `h` at bucket `b`: total frequency
of items hashed to `b`. -/
def counter {X : Type*} [DecidableEq X] [Fintype X]
    (f : X → ℕ) (h : X → ℕ) (b : ℕ) : ℕ :=
  ∑ y, if h y = b then f y else 0

/-- Count-Min estimate with the `d` hash functions `H 0, ..., H (d - 1)`
into `ℕ` buckets: the minimum counter among the buckets `x` hashes
to. Requires `0 < d`. -/
def estimate {X : Type*} [DecidableEq X] [Fintype X]
    (f : X → ℕ) (H : ℕ → (X → ℕ)) (d : ℕ) (hd : 0 < d) (x : X) : ℕ :=
  Finset.inf' (Finset.Icc 0 (d - 1)) ⟨0, Finset.mem_Icc.mpr ⟨le_refl 0, by omega⟩⟩
    (fun j => counter f (H j) (H j x))

/-- With natural-number frequencies on a finite universe and `0 < d` rows, the estimate
never undercounts: `f x ≤ estimate f H d hd x`. -/
theorem freq_le_estimate {X : Type*} [DecidableEq X] [Fintype X]
    (f : X → ℕ) (H : ℕ → (X → ℕ)) (d : ℕ) (hd : 0 < d) (x : X) :
    f x ≤ estimate f H d hd x := by
  unfold estimate
  refine Finset.le_inf' _ _ (fun j _ => ?_)
  show f x ≤ counter f (H j) (H j x)
  unfold counter
  calc f x = (if H j x = H j x then f x else 0) := (ite_eq_left rfl).symm
    _ ≤ ∑ y, (if H j y = H j x then f y else 0) :=
        Finset.single_le_sum (f := fun y => if H j y = H j x then f y else 0)
          (fun y _ => Nat.zero_le _) (Finset.mem_univ x)

/-- The estimate is at most every individual counter. -/
theorem estimate_le_counter {X : Type*} [DecidableEq X] [Fintype X]
    (f : X → ℕ) (H : ℕ → (X → ℕ)) (d : ℕ) (hd : 0 < d) (x : X)
    (j : ℕ) (hj : j ≤ d - 1) :
    estimate f H d hd x ≤ counter f (H j) (H j x) := by
  unfold estimate
  apply Finset.inf'_le
  exact Finset.mem_Icc.mpr ⟨Nat.zero_le j, hj⟩

/-- A counter exceeds `f x` only by colliding mass. -/
theorem counter_le_freq_add_collision {X : Type*} [DecidableEq X] [Fintype X]
    (f : X → ℕ) (h : X → ℕ) (x : X) :
    counter f h (h x) ≤ f x
      + ∑ y ∈ Finset.univ.filter (fun y => y ≠ x ∧ h y = h x), f y := by
  unfold counter
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x), ite_eq_left rfl]
  apply Nat.add_le_add_left
  have hsub : Finset.univ.filter (fun y => y ≠ x ∧ h y = h x) ⊆ Finset.univ.erase x := by
    intro y hy
    obtain ⟨-, hy_ne, -⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_erase.mpr ⟨hy_ne, Finset.mem_univ y⟩
  have hzero : ∀ y ∈ Finset.univ.erase x,
      y ∉ Finset.univ.filter (fun y => y ≠ x ∧ h y = h x) →
      (if h y = h x then f y else 0) = 0 := by
    intro y hy_erase hy_notin
    have hy_ne : y ≠ x := (Finset.mem_erase.mp hy_erase).1
    have hne : ¬ (h y = h x) := by
      intro hh
      exact hy_notin (Finset.mem_filter.mpr ⟨Finset.mem_univ y, ⟨hy_ne, hh⟩⟩)
    exact ite_eq_right hne
  have heq : (∑ y ∈ Finset.univ.filter (fun y => y ≠ x ∧ h y = h x),
        (if h y = h x then f y else 0))
      = ∑ y ∈ Finset.univ.erase x, (if h y = h x then f y else 0) :=
    Finset.sum_subset hsub hzero
  have hcongr : (∑ y ∈ Finset.univ.filter (fun y => y ≠ x ∧ h y = h x),
        (if h y = h x then f y else 0))
      = ∑ y ∈ Finset.univ.filter (fun y => y ≠ x ∧ h y = h x), f y := by
    apply Finset.sum_congr rfl
    intro y hy
    obtain ⟨-, -, hhy⟩ := Finset.mem_filter.mp hy
    exact ite_eq_left hhy
  rw [← heq, hcongr]

end CountMin

end Cslib.Algorithms.Lean

end
