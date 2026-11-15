/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

/-!
# Comparison decision trees

A comparison decision tree branches on comparisons and
outputs an answer at each leaf. A tree of depth `d` has at
most `2^d` leaves, so a tree distinguishing all `n!` input
orders has `n! ≤ 2^d`.
-/

@[expose] public section

/-- Comparison decision trees (core of ALG-01): internal
nodes branch on a comparison, leaves output an answer. -/
inductive DTree (α : Type) : Type
  | leaf (v : α) : DTree α
  | node (l r : DTree α) : DTree α

/-- Number of leaves. -/
def DTree.leaves {α : Type} : DTree α → ℕ
  | .leaf _ => 1
  | .node l r => l.leaves + r.leaves

/-- Depth (longest root-to-leaf path). -/
def DTree.depth {α : Type} : DTree α → ℕ
  | .leaf _ => 0
  | .node l r => 1 + max l.depth r.depth

/-- A binary tree of depth `d` has at most `2^d` leaves. -/
theorem DTree.leaves_le_two_pow_depth {α : Type} (t : DTree α) :
    t.leaves ≤ 2 ^ t.depth := by
  induction t with
  | leaf v => simp [DTree.leaves, DTree.depth]
  | node l r ihl ihr =>
    simp only [DTree.leaves, DTree.depth]
    have h1 : (2 : ℕ) ^ l.depth ≤ 2 ^ max l.depth r.depth :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_max_left _ _)
    have h2 : (2 : ℕ) ^ r.depth ≤ 2 ^ max l.depth r.depth :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_max_right _ _)
    have h3 : (2 : ℕ) ^ (1 + max l.depth r.depth) = 2 * 2 ^ max l.depth r.depth := by
      rw [add_comm 1 _, pow_succ']
    omega

/-- Sorting lower bound, counting form: any decision tree
whose leaves distinguish all `n! ` input orders has depth `d`
with `n! ≤ 2^d`. -/
theorem DTree.factorial_le_two_pow_depth {α : Type} (t : DTree α)
    (n : ℕ) (h : Nat.factorial n ≤ t.leaves) :
    Nat.factorial n ≤ 2 ^ t.depth := by
  exact Nat.le_trans h (DTree.leaves_le_two_pow_depth t)

end
