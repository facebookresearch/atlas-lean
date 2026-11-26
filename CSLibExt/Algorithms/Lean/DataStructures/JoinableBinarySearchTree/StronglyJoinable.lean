/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`thys/Joinable_BST_Work_Bounds/BalancedBinary.thy` and
`thys/Joinable_BST_Work_Bounds/StronglyJoinable.thy` (Archive of Formal Proofs, entry
`Joinable_BST_Work_Bounds`, https://www.isa-afp.org/entries/Joinable_BST_Work_Bounds.html):
Copyright (c) 2004, Gerwin Klein, Tobias Nipkow, Lawrence C. Paulson
Copyright (c) 2004, contributing authors (see author notice in individual files)
All rights reserved.
Licensed under the BSD License of the Archive of Formal Proofs (https://isa-afp.org/LICENSE).
Authors: Marco Haucke
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.JoinableBinarySearchTree.Basic
public import Mathlib.Tactic

/-!
# Joinable binary search trees: the strongly joinable framework

The strongly joinable framework of Blelloch et al. (2022) as formalized
in the AFP entry `Joinable_BST_Work_Bounds` (`StronglyJoinable.thy`):
`StronglyJoinableData` folds the `BalancedShape`, `BalancedTree`, and
`StronglyJoinable` locales into a single structure (fields are
hypotheses, not axioms). `balancedOf` is the `BalancedTree` balancing
predicate: at every node, the rank lies between `max + c_l` and
`min + c_u` of the children's ranks. The instances live in
`StronglyJoinableRBT` and `StronglyJoinableAVL`; the generic
`O(m log (n/m + 1))` analysis for `union` / `inter` / `diff` is out of
scope (the book cites Blelloch et al. for it).

## Provenance

`BalancedBinary.thy` (the `BalancedShape` / `BalancedTree` locales) and
`StronglyJoinable.thy` in the AFP entry `Joinable_BST_Work_Bounds`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Cslib.Algorithms.Lean
namespace JoinableBinarySearchTree

variable {α : Type u} {β : Type v} [LinearOrder α] [Inhabited β]

-- ## Strongly joinable trees (`Joinable_BST_Work_Bounds`)
-- The `StronglyJoinable` locale of `StronglyJoinable.thy` combines
-- `Set2_Join` with the `BalancedTree` balancing scheme and adds the
-- strongly-joinable rules of Blelloch et al. (2022): `rule_mono`,
-- `rule_sub`, `join_size`, `rule_cost`. The `BalancedShape` /
-- `BalancedTree` locales are folded into this single structure: `rank`,
-- `c_l`, `c_u`, `c_vals`, `rank_leaf` and `inv_balanced` are the
-- `BalancedTree` part, the rest is the `StronglyJoinable` part.

/-- The balance predicate of `BalancedShape` (Blelloch et al., Property 4
setup): at every node, the rank lies between `max + c_l` and
`min + c_u` of the children's ranks. -/
public def balancedOf {α : Type u} {β : Type v} (rank : Tree α β → ℝ) (c_l c_u : ℝ) : Tree α β → Prop
  | .Leaf => True
  | .Node l kv r =>
    max (rank l) (rank r) + c_l ≤ rank (.Node l kv r) ∧
    rank (.Node l kv r) ≤ min (rank l) (rank r) + c_u ∧
    balancedOf rank c_l c_u l ∧ balancedOf rank c_l c_u r

/-- The `StronglyJoinable` locale (`StronglyJoinable.thy`), packaged like
`JoinData`: fields are hypotheses, not axioms. `T_join` is the timing
function supplied by an instantiation; the analysis is stated relative
to it, exactly as in the AFP. -/
public structure StronglyJoinableData (α : Type u) (β : Type v) [LinearOrder α] [Inhabited β]
    extends JoinData α β where
  rank : Tree α β → ℝ
  c_l : ℝ
  c_u : ℝ
  c_vals : 0 < c_l ∧ c_l ≤ 1 ∧ 1 ≤ c_u
  rank_leaf : rank .Leaf = 0
  inv_balanced : ∀ t, inv t → balancedOf rank c_l c_u t
  T_join : Tree α β → α → Tree α β → ℕ
  k₀ : ℝ
  k₁ : ℝ
  rule_mono : ∀ {l r a}, inv l → inv r → max (rank l) (rank r) ≤ rank (join l a r)
  rule_sub : ∀ {l' l r' r a b x}, rank l' ≤ rank l + x → rank r' ≤ rank r + x →
    inv l' → inv r' → inv (.Node l (a, b) r) →
    rank (join l' a r') ≤ rank (.Node l (a, b) r) + x
  join_size : ∀ {l r a}, inv l → inv r → tsize (join l a r) = tsize l + tsize r + 1
  rule_cost : ∀ {l r a}, inv l → inv r →
    (T_join l a r : ℝ) ≤ k₀ + k₁ * |rank l - rank r|
  k₀_nonneg : 0 ≤ k₀
  k₁_nonneg : 0 ≤ k₁

end JoinableBinarySearchTree

end Cslib.Algorithms.Lean
