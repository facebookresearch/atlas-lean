/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.SplayTree.Amortized
public import Mathlib.Tactic.IntervalCases

/-!
# Tests for the amortized analysis of splaying

Concrete runs of the rotation count, cost and focus on a left path, including the odd-depth
case where the recursive splay performs its single rotation at the bottom of the path, and
instances of the access lemma and the balance theorem. Also concrete runs of the
`splayMax`, `delete`, and book's `insert` costs, and instances of their amortized bounds.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.SplayTreeAmortizedTests

open SplayTree

/-- The left path `4 → 3 → 2 → 1`. -/
def path4 : BinaryTree ℕ :=
  .node 4 (.node 3 (.node 2 (.node 1 .nil .nil) .nil) .nil) .nil

/-- Accessing the deepest key (depth 3) performs one zig-zig and one zig. -/
example : rotations 1 path4 = 3 := rfl

example : cost 1 path4 = 3 := rfl

/-- The key at the root costs one unit and performs no rotation. -/
example : rotations 4 path4 = 0 := rfl

example : cost 4 path4 = 1 := rfl

/-- At odd depth the single rotation happens at the bottom of the path: the result is
`1 (·, 3 (2, 4))`, whereas Sleator–Tarjan bottom-up splaying would give `1 (·, 4 (2 (·, 3), ·))`. -/
example : splay 1 path4 =
    .node 1 .nil (.node 3 (.node 2 .nil .nil) (.node 4 .nil .nil)) := rfl

/-- An absent key larger than every key: the search stops at the root. -/
example : focus 5 path4 = path4 := rfl

/-- An absent key between `1` and `2`: the search stops at `1`. -/
example : focus 0 path4 = .node 1 .nil .nil := rfl

example : focus 1 path4 = .node 1 .nil .nil := rfl

/-- The access lemma on the path, where `focus` is a single node. -/
example : (cost 1 path4 : ℝ) + potential (splay 1 path4) - potential path4 ≤
    3 * (Real.logb 2 (path4.numNodes : ℝ) - Real.logb 2 ((focus 1 path4).numNodes : ℝ)) + 1 :=
  access_lemma 1 path4

/-- The balance theorem for ten splays at alternating keys of the path. -/
example : (∑ i ∈ Finset.range 10, (cost (i % 4 + 1) (splayRun (fun j => j % 4 + 1) path4 i) : ℝ))
    ≤ 10 * (3 * Real.logb 2 (path4.numNodes : ℝ) + 1) +
      path4.numNodes * Real.logb 2 (path4.numNodes : ℝ) := by
  have := balance_theorem (fun j => j % 4 + 1) path4 10
  push_cast at this ⊢
  exact this

/-- The path is a search tree. -/
theorem ordered_path4 : BinarySearchTree.Ordered path4 := by
  simp [path4, BinarySearchTree.Ordered, BinarySearchTree.All]

/-- Accessing `1, 2, 3, 4` once each: static optimality applies with `q(i) = 1`. -/
example : (∑ j ∈ Finset.range 4, (cost (j + 1) (splayRun (fun j => j + 1) path4 j) : ℝ)) ≤
    4 + 3 * ((BinarySearchTree.inorder path4).map (fun i => (accessCount (fun j => j + 1) 4 i : ℝ) *
        (Real.logb 2 4 - Real.logb 2 (accessCount (fun j => j + 1) 4 i)))).sum +
      ((BinarySearchTree.inorder path4).map
        (fun i => Real.logb 2 4 - Real.logb 2 (accessCount (fun j => j + 1) 4 i))).sum := by
  have h := static_optimality (fun j => j + 1) ordered_path4 4 (by
    intro j hj
    interval_cases j <;> simp [path4, Membership.mem, BinarySearchTree.Mem]) (by
    intro i hi
    have h4 : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
      have hin : BinarySearchTree.inorder path4 = [1, 2, 3, 4] := rfl
      rw [← BinarySearchTree.mem_inorder, hin] at hi
      simpa using hi
    rcases h4 with rfl | rfl | rfl | rfl <;> decide)
  push_cast at h ⊢
  exact h

/-- The weighted access lemma with weights `1, 2, 3, 4` on the path. -/
example : (cost 1 path4 : ℝ) + potentialW (fun i : ℕ => (i : ℝ) + 1) (splay 1 path4) -
    potentialW (fun i : ℕ => (i : ℝ) + 1) path4 ≤
      3 * (Real.logb 2 (weight (fun i : ℕ => (i : ℝ) + 1) path4) -
        Real.logb 2 (weight (fun i : ℕ => (i : ℝ) + 1) (focus 1 path4))) + 1 :=
  access_lemma_weighted (fun i => by positivity) 1 path4

/-- A single node has potential zero. -/
example : potential (.node (7 : ℕ) .nil .nil) = 0 := by
  simp [potential]

/-! ### Splay-max, delete, and the book's insert: costs and amortized bounds -/

/-- The right path `1 → 2 → 3 → 4`. -/
def rpath : BinaryTree ℕ :=
  .node 1 .nil (.node 2 .nil (.node 3 .nil (.node 4 .nil .nil)))

/-- Splaying the maximum of a right path performs one zig-zig and one zig. -/
example : rotationsMax rpath = 3 := rfl

example : costMax rpath = 3 := rfl

example : splayMax rpath =
    .node 4 (.node 2 (.node 1 .nil .nil) (.node 3 .nil .nil)) .nil := rfl

/-- Splaying the maximum of a left path performs no rotation. -/
example : rotationsMax path4 = 0 := rfl

example : costMax path4 = 1 := rfl

example : splayMax path4 = path4 := rfl

/-- Deleting the deepest key of the path: the splay costs 3, the `splayMax`
on the empty left subtree costs 1. -/
example : costDelete 1 path4 = 4 := rfl

/-- Deleting an absent key larger than every key costs the splay alone. -/
example : costDelete 5 path4 = 1 := rfl

example : delete 1 path4 = .node 3 (.node 2 .nil .nil) (.node 4 .nil .nil) := rfl

/-- Inserting below the minimum costs the splay alone; the rebuild is free. -/
example : costInsert 0 path4 = cost 0 path4 := rfl

/-- The right path is a search tree. -/
theorem ordered_rpath : BinarySearchTree.Ordered rpath := by
  simp [rpath, BinarySearchTree.Ordered, BinarySearchTree.All]

/-- Splaying for the maximum costs as many rotations as splaying for that key. -/
example : rotationsMax rpath = rotations 4 rpath :=
  rotationsMax_eq_rotations ordered_rpath (by
    intro y hy
    simp [rpath, Membership.mem, BinarySearchTree.Mem] at hy
    omega)

/-- The `splayMax` amortized bound on the path. -/
example : (costMax path4 : ℝ) + potential (splayMax path4) - potential path4 ≤
    3 * Real.logb 2 (path4.numNodes : ℝ) + 1 :=
  amortized_splayMax_le path4 ordered_path4

/-- The `delete` amortized bound on the path. -/
example : (costDelete 1 path4 : ℝ) + potential (delete 1 path4) - potential path4 ≤
    5 * Real.logb 2 (path4.numNodes : ℝ) + 2 :=
  amortized_delete_le 1 path4 ordered_path4

/-- The book's `insert` amortized bound on the path. -/
example : (costInsert 0 path4 : ℝ) + potential (nipkowInsert 0 path4) - potential path4 ≤
    4 * Real.logb 2 (path4.numNodes : ℝ) + 2 :=
  amortized_nipkowInsert_le 0 path4

end Cslib.Algorithms.Lean.SplayTreeAmortizedTests
