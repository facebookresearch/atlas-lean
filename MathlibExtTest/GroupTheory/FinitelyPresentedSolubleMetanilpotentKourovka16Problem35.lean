/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.FinitelyPresentedSolubleMetanilpotentKourovka16Problem35

open MathlibExt.GroupTheory.FinitelyPresentedSolubleMetanilpotentKourovka16Problem35Wanted

-- Extract a counterexample with both normality conditions and the finite-index condition.
example : ∃ (G : Type) (_ : Group G), Group.IsFinitelyPresented G ∧ Group.IsSolvable G ∧
    ∀ (M : Subgroup G), M.Normal → M.FiniteIndex →
      ∀ (N : Subgroup M) [N.Normal], Group.IsNilpotent N → ¬ Group.IsNilpotent (M ⧸ N) := by
  by_contra! h
  apply finitelyPresentedSolubleMetanilpotentByFinite_refuted
  intro G _ hfp hs
  exact h G ‹Group G› hfp hs

-- The trivial subgroup supplies a finite-index witness in every finite group.
example (G : Type) [Group G] [Finite G] : IsMetanilpotentByFinite G := by
  refine ⟨⊥, inferInstance, inferInstance, ⊥, inferInstance, inferInstance, inferInstance⟩
