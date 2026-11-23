/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.UnionFind.Union
public import CSLibExt.Algorithms.Lean.DataStructures.UnionFind.Find
import Mathlib.Data.Nat.Log

/-!
# Reachable-state rank bounds for canonical union-find

Canonical empty, push, find and union operations preserve the exponential lower
bound on a root's component size. Thus root rank and first-root parent-chain
depth are at most the base-two logarithm of the allocated size. Raw `link` is
not a reachability constructor: it permits its first argument to be a nonroot.
These are structural bounds, not machine-time or amortized bounds.
-/

@[expose] public section

namespace Batteries.UnionFind

/-- States produced by the canonical public operations, excluding raw `link`. -/
inductive Reachable : UnionFind → Prop
  | mkEmpty (c : Nat) : Reachable (mkEmpty c)
  | push {u : UnionFind} : Reachable u → Reachable u.push
  | find {u : UnionFind} (x : Fin u.size) : Reachable u → Reachable (u.find x).1
  | union {u : UnionFind} (x y : Fin u.size) : Reachable u → Reachable (u.union x y)

/-- Allocated natural-number indices whose canonical root is `r`. -/
def component (u : UnionFind) (r : Nat) : Finset Nat :=
  (Finset.range u.size).filter fun i ↦ u.rootD i = r

/-- Component membership records both allocation and the canonical representative. -/
@[simp] theorem mem_component {u : UnionFind} {r i : Nat} :
    i ∈ u.component r ↔ i < u.size ∧ u.rootD i = r := by
  simp [component]

/-- The canonical empty state is reachable. -/
theorem Reachable.empty : Reachable empty := .mkEmpty 0

private theorem rank_find_eq (u : UnionFind) (x : Fin u.size) (i : Nat) :
    (u.find x).1.rank i = u.rank i := by
  by_cases hi : i < u.size
  · have hfi : i < (u.find x).1.size := by simpa using hi
    simp only [rank, rankD_eq hfi, rankD_eq hi, getElem_find u x i hi]
  · simp only [rank, rankD, find_size, hi, ↓reduceDIte]

private theorem size_union (u : UnionFind) (x y : Fin u.size) :
    (u.union x y).size = u.size := by
  simp only [union, size, arr_link, linkAux_size, find_size]

private theorem rootD_union_eq_ite (u : UnionFind) (x y : Fin u.size) (i : Nat) :
    (u.union x y).rootD i =
      if u.rootD i = u.rootD x ∨ u.rootD i = u.rootD y then
        if u.rank (u.rootD y) < u.rank (u.rootD x) then u.rootD x else u.rootD y
      else u.rootD i := by
  simp only [union]
  rw [rootD_link_eq_ite _ _ _ (by simp [← rootD_eq_self, rootD_rootD])]
  simp only [rank_find_eq, find_root_2, find_root_1]

private theorem rootD_eq_of_union_root (u : UnionFind) (x y : Fin u.size) {r : Nat}
    (hr : (u.union x y).parent r = r) : u.rootD r = r := by
  have h := rootD_union_eq_ite u x y r
  rw [rootD_eq_self.mpr hr] at h
  split at h
  · split at h
    · rw [h, rootD_rootD]
    · rw [h, rootD_rootD]
  · exact h.symm

private theorem component_subset_union (u : UnionFind) (x y : Fin u.size) {r : Nat}
    (hr : (u.union x y).parent r = r) : u.component r ⊆ (u.union x y).component r := by
  intro i hi
  obtain ⟨hi, hir⟩ := mem_component.mp hi
  refine mem_component.mpr ⟨by simpa only [size_union] using hi, ?_⟩
  have he : (u.union x y).rootD i = (u.union x y).rootD r :=
    equiv_union.mpr (Or.inl (hir.trans (rootD_eq_of_union_root u x y hr).symm))
  exact he.trans (rootD_eq_self.mpr hr)

private theorem component_union_of_rank_eq (u : UnionFind) (x y : Fin u.size)
    (h : u.rank (u.rootD x) = u.rank (u.rootD y)) :
    (u.union x y).component (u.rootD y) =
      u.component (u.rootD x) ∪ u.component (u.rootD y) := by
  ext i
  simp only [mem_component, Finset.mem_union, size_union, rootD_union_eq_ite, h,
    Nat.lt_irrefl, ↓reduceIte]
  by_cases hx : u.rootD i = u.rootD x <;>
    by_cases hy : u.rootD i = u.rootD y <;> simp [hx, hy] <;> omega

private theorem disjoint_components (u : UnionFind) {r s : Nat} (h : r ≠ s) :
    Disjoint (u.component r) (u.component s) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact h ((mem_component.mp hi).2.symm.trans (mem_component.mp hj).2)

private theorem bound_union (u : UnionFind) (x y : Fin u.size)
    (ih : ∀ r, r < u.size → u.parent r = r → 2 ^ u.rank r ≤ (u.component r).card)
    {r : Nat} (hr : r < (u.union x y).size) (hroot : (u.union x y).parent r = r) :
    2 ^ (u.union x y).rank r ≤ ((u.union x y).component r).card := by
  rw [rank_union]
  split
  · rename_i h
    obtain ⟨hne, hrank, rfl⟩ := h
    rw [component_union_of_rank_eq u x y hrank,
      Finset.card_union_of_disjoint (disjoint_components u hne)]
    have hx := ih (u.rootD x) (rootD_lt.mpr x.isLt) (parent_rootD u x)
    have hy := ih (u.rootD y) (rootD_lt.mpr y.isLt) (parent_rootD u y)
    rw [hrank] at hx
    simpa only [pow_succ, Nat.mul_two] using Nat.add_le_add hx hy
  · exact (ih r (by simpa only [size_union] using hr)
      (rootD_eq_self.mp (rootD_eq_of_union_root u x y hroot))).trans
        (Finset.card_le_card (component_subset_union u x y hroot))

private theorem bound_push (u : UnionFind)
    (ih : ∀ r, r < u.size → u.parent r = r → 2 ^ u.rank r ≤ (u.component r).card)
    {r : Nat} (hr : r < u.push.size) (hroot : u.push.parent r = r) :
    2 ^ u.push.rank r ≤ (u.push.component r).card := by
  rw [rank_push]
  by_cases hold : r < u.size
  · refine (ih r hold (by simpa only [parent_push] using hroot)).trans
      (Finset.card_le_card ?_)
    intro i hi
    obtain ⟨hi, hir⟩ := mem_component.mp hi
    have his : i < u.push.size := by
      simpa only [size, arr_push, Array.size_push] using Nat.lt_succ_of_lt hi
    exact mem_component.mpr ⟨his, by simpa only [root_push] using hir⟩
  · have hz : u.rank r = 0 := by simp [rank, rankD, hold]
    rw [hz]
    exact Finset.card_pos.mpr ⟨r, mem_component.mpr ⟨hr, rootD_eq_self.mpr hroot⟩⟩

/-- Every allocated root of a reachable state heads at least two to its rank many nodes. -/
theorem Reachable.two_pow_rank_le_card_component {u : UnionFind} (hu : Reachable u)
    {r : Nat} (hr : r < u.size) (hroot : u.parent r = r) :
    2 ^ u.rank r ≤ (u.component r).card := by
  induction hu generalizing r with
  | mkEmpty c => simp [size, UnionFind.mkEmpty] at hr
  | push hu ih => exact bound_push _ (fun r ↦ ih (r := r)) hr hroot
  | @find u x hu ih =>
    have he : (u.find x).1.component r = u.component r := by
      ext i
      simp only [mem_component, find_size, find_root_1]
    rw [rank_find_eq, he]
    exact ih (by simpa using hr) (rootD_eq_self.mp (by
      simpa only [find_root_1] using rootD_eq_self.mpr hroot))
  | union x y hu ih => exact bound_union _ x y (fun r ↦ ih (r := r)) hr hroot

/-- Every allocated node of a reachable state has root rank at most `log₂ size`. -/
theorem Reachable.rank_rootD_le_log2 {u : UnionFind} (hu : Reachable u)
    {x : Nat} (hx : x < u.size) : u.rank (u.rootD x) ≤ Nat.log2 u.size := by
  rw [Nat.log2_eq_log_two]
  apply Nat.le_log_of_pow_le Nat.one_lt_two
  exact (hu.two_pow_rank_le_card_component (rootD_lt.mpr hx) (parent_rootD u x)).trans
    (by simpa only [component, Finset.card_range] using
      Finset.card_filter_le (Finset.range u.size) (fun i ↦ u.rootD i = u.rootD x))

/-- Saved ranks increase by at least one at every nonroot step of the original parent chain. -/
theorem rank_add_le_rank_iterate (u : UnionFind) (x k : Nat)
    (hk : ∀ j < k, u.parent (u.parent^[j] x) ≠ u.parent^[j] x) :
    u.rank x + k ≤ u.rank (u.parent^[k] x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hih := ih (fun j hj ↦ hk j (Nat.lt_succ_of_lt hj))
    have hstep := u.rank_lt (hk k (Nat.lt_succ_self k))
    rw [Function.iterate_succ_apply']
    omega

/-- First-root depth is at most the saved rank gap, even without reachability. -/
theorem exists_first_iterate_rootD_le_rank (u : UnionFind) (x : Fin u.size) :
    ∃ d, u.parent^[d] x = u.rootD x ∧ (∀ k < d, u.parent^[k] x ≠ u.rootD x) ∧
      u.rank x + d ≤ u.rank (u.rootD x) := by
  obtain ⟨d, hd, hfirst, _⟩ := exists_first_iterate_rootD u x
  refine ⟨d, hd, hfirst, ?_⟩
  rw [← hd]
  apply rank_add_le_rank_iterate
  intro k hk hp
  have hstay := Function.iterate_fixed hp (d - k)
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel (Nat.le_of_lt hk), hd] at hstay
  exact hfirst k hk hstay.symm

/-- In a reachable state, the first original-parent-chain root occurs by `log₂ size`. -/
theorem Reachable.exists_first_iterate_rootD_le_log2 {u : UnionFind} (hu : Reachable u)
    (x : Fin u.size) :
    ∃ d, u.parent^[d] x = u.rootD x ∧ (∀ k < d, u.parent^[k] x ≠ u.rootD x) ∧
      d ≤ Nat.log2 u.size := by
  obtain ⟨d, hd, hfirst, hrank⟩ := exists_first_iterate_rootD_le_rank u x
  have hlog := hu.rank_rootD_le_log2 x.isLt
  exact ⟨d, hd, hfirst, by omega⟩

end Batteries.UnionFind
