/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sidon sets
-/
module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.TypeStar

@[expose] public section

namespace Set

/-- A set in an additive commutative monoid is Sidon when every equality of
two pairwise sums is trivial up to swapping the summands. Repeated summands
are included. -/
def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

end Set
