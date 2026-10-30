/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic

/-!
# Quadtree carrier and structural invariants

A `QTree α` is a finite four-way tree with values at its leaves. A leaf
represents a constant region; a branch orders its quadrants as low/low,
low/high, high/low, high/high in the two coordinates. The scale is supplied
to lookup, not stored in the tree. `height` counts branch levels, and
`compressed` excludes four identical leaf children at every branch.

This shared carrier is adapted from both
`auto-fdsa-13-01/solution/Solution.lean` and
`auto-fdsa-13-02/solution/Solution.lean` in `codimango/sw-verification-zhih`
at pinned commit
`16412d086eb5af2e74da78731bde50da0667bc79` (the corresponding specifications
are in each task's `environment/Task.lean`). The Boolean set operations and
polymorphic function reconstruction live in separate modules because their
lookup functions intentionally differ on a branch at scale zero.

These are region quadtrees, not point-insertion spatial search trees. No
balancing, dynamic updates, or complexity bounds are claimed.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

/-- A finite region quadtree with a value leaf or four ordered quadrants. -/
inductive QTree (α : Type u) where
  | L : α → QTree α
  | Q : QTree α → QTree α → QTree α → QTree α → QTree α
  deriving DecidableEq

namespace QTree

/-- The maximum number of branches from the root to a leaf. -/
def height {α : Type u} : QTree α → Nat
  | .L _ => 0
  | .Q t0 t1 t2 t3 =>
      Nat.succ (max (max (height t0) (height t1))
        (max (height t2) (height t3)))

/-- Every subtree is compressed and no branch has four identical leaves.
Identical nonleaf children are allowed: they need not represent a constant. -/
def compressed {α : Type u} : QTree α → Prop
  | .L _ => True
  | .Q t0 t1 t2 t3 =>
      compressed t0 ∧ compressed t1 ∧ compressed t2 ∧ compressed t3 ∧
        ¬ (∃ x, t0 = .L x ∧ t1 = t0 ∧ t2 = t0 ∧ t3 = t0)

/-- Selects low/low, low/high, high/low, or high/high, respectively, when
`(x, y)` is `(true, true)`, `(true, false)`, `(false, true)`, or
`(false, false)`.
In lookup, `true` means that the corresponding coordinate is below the split. -/
def selectTree {α : Type u} (x y : Bool)
    (t0 t1 t2 t3 : QTree α) : QTree α :=
  if x then if y then t0 else t1 else if y then t2 else t3

/-- A bound on branch height bounds all four child heights one level lower. -/
theorem height_children_le {α : Type u} {t0 t1 t2 t3 : QTree α}
    {n : Nat} (h : height (.Q t0 t1 t2 t3) ≤ n + 1) :
    height t0 ≤ n ∧ height t1 ≤ n ∧ height t2 ≤ n ∧ height t3 ≤ n := by
  simp only [height, Nat.succ_le_succ_iff, Nat.max_le] at h
  exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩

end QTree

end Cslib.Algorithms.Lean
