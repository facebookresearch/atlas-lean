/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Basic

/-!
# Fenwick tree: prefix-sum algebra

A Fenwick (binary indexed) tree answers prefix-sum queries and
point updates. This module fixes the query/update algebra on
the prefix-sum view: a point update adds `d` exactly to the
queries at positions at or after the update point. The
compressed tree representation and its logarithmic walks are
not formalized here.
-/

@[expose] public section

/-- Prefix-sum view of a Fenwick (BIT) array (core of ALG-29b):
the query at `i` returns the sum of entries `0..i`. The
compressed tree representation and its `O(log n)` walks are
downstream; this pin fixes the query/update algebra any BIT
must satisfy. -/
def prefixSum {n : ℕ} (a : Fin n → ℤ) (i : Fin n) : ℤ :=
  ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), a j

/-- Point update adds `d` at position `p`; exactly the queries
at positions `>= p` increase, by `d`. -/
theorem prefixSum_update {n : ℕ} (a : Fin n → ℤ) (p i : Fin n) (d : ℤ) :
    prefixSum (Function.update a p (a p + d)) i
      = prefixSum a i + (if p ≤ i then d else 0) := by
  unfold prefixSum
  by_cases h : p ≤ i
  · rw [ite_eq_left h]
    have hmem : p ∈ Finset.univ.filter (fun j => j ≤ i) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ p, h⟩
    have h1 : ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), Function.update a p (a p + d) j
        = ∑ j ∈ (Finset.univ.filter (fun j => j ≤ i)) \ {p}, a j + (a p + d) := by
      rw [Finset.sum_eq_sum_sdiff_singleton_add hmem]
      congr 1
      · refine Finset.sum_congr rfl (fun j hj => ?_)
        simp only [Finset.mem_sdiff, Finset.mem_singleton] at hj
        exact Function.update_of_ne hj.2 _ _
      · exact Function.update_self p _ a
    have h2 : ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), a j
        = ∑ j ∈ (Finset.univ.filter (fun j => j ≤ i)) \ {p}, a j + a p :=
      Finset.sum_eq_sum_sdiff_singleton_add hmem a
    rw [h1, h2]
    ring
  · rw [ite_eq_right h, add_zero]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hji : j ≤ i := (Finset.mem_filter.mp hj).2
    have hne : j ≠ p := by
      intro heq
      rw [heq] at hji
      exact h hji
    exact Function.update_of_ne hne _ _

/-- Queries below the update point are unchanged. -/
theorem prefixSum_update_of_lt {n : ℕ} (a : Fin n → ℤ) (p i : Fin n)
    (d : ℤ) (h : i < p) :
    prefixSum (Function.update a p (a p + d)) i = prefixSum a i := by
  rw [prefixSum_update, ite_eq_right (not_le_of_gt h), add_zero]

end
