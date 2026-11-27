/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.MaximalCentralizerNilpotentSubgroupKourovka14Problem67

open MathlibExt.GroupTheory.MaximalCentralizerNilpotentSubgroupKourovka14Problem67Wanted

-- Recover the counterexample: a nilpotent subgroup normalized by a centralizer of maximal order
-- that is not contained in that centralizer.
example : ∃ (G : Type) (_ : Group G) (_ : Finite G) (a : G), a ≠ 1 ∧
    (∀ x : G, x ≠ 1 →
      Nat.card (Subgroup.centralizer {x}) ≤ Nat.card (Subgroup.centralizer {a})) ∧
    ∃ H : Subgroup G, Group.IsNilpotent H ∧
      Subgroup.centralizer {a} ≤ Subgroup.normalizer (H : Set G) ∧
      ¬ H ≤ Subgroup.centralizer {a} := by
  by_contra! h
  exact maximalCentralizerContainsNormalizedNilpotent_refuted fun G _ _ a ha hmax H hH hN =>
    h G inferInstance inferInstance a ha hmax H hH hN

-- In such a counterexample some element of `H` does not commute with `a`.
example : ∃ (G : Type) (_ : Group G) (_ : Finite G) (a : G), a ≠ 1 ∧
    (∀ x : G, x ≠ 1 →
      Nat.card (Subgroup.centralizer {x}) ≤ Nat.card (Subgroup.centralizer {a})) ∧
    ∃ H : Subgroup G, Group.IsNilpotent H ∧
      Subgroup.centralizer {a} ≤ Subgroup.normalizer (H : Set G) ∧
      ∃ h ∈ H, h * a ≠ a * h := by
  by_contra! hall
  refine maximalCentralizerContainsNormalizedNilpotent_refuted fun G _ _ a ha hmax H hH hN h hh =>
    ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hall G inferInstance inferInstance a ha hmax H hH hN h hh
