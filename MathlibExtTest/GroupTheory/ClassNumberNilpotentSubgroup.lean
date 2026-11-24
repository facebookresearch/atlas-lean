/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.ClassNumberNilpotentSubgroup

/-!
# Tests for the class number bound

Recover the existential counterexample from the public statement and check the equality
case of the proposed bound for finite abelian groups.
-/

open MathlibExt.GroupTheory.ClassNumberNilpotentSubgroupKourovka14Problem54Wanted

example : ∃ (G : Type) (_ : Group G) (_ : Finite G), ∀ N : Subgroup G,
    Group.IsNilpotent N → Nat.card N < Nat.card (ConjClasses G) := by
  classical
  by_contra! h
  apply classNumberAtMostNilpotentSubgroupOrder_refuted
  intro G _ _
  exact h G inferInstance inferInstance

example (G : Type) [CommGroup G] [Finite G] :
    ∃ N : Subgroup G, Group.IsNilpotent N ∧ Nat.card (ConjClasses G) = Nat.card N := by
  refine ⟨⊤, inferInstance, ?_⟩
  rw [Subgroup.card_top]
  exact Nat.card_congr ConjClasses.mkEquiv.symm
