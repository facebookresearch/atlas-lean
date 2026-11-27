/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.SubsetFactorizationCounterexamplesKourovka19Problem35
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Basic

open MathlibExt.GroupTheory.SubsetFactorizationCounterexamplesKourovka19Problem35Wanted

-- The first admissible length gives a counterexample with three nontrivial sizes.
example : ∃ (G : Type) (_ : Group G) (_ : Finite G) (a : Fin 3 → ℕ),
    (∀ i, 2 ≤ a i) ∧ ∏ i, a i = Nat.card G ∧ ¬ HasSubsetFactorization G 3 a :=
  subsetFactorizationCounterexampleEveryLength_holds 3 le_rfl

-- The two-element group is covered by one factor of size two, the whole group.
example : HasSubsetFactorization (Multiplicative (ZMod 2)) 1 (fun _ => 2) := by
  refine ⟨fun _ => Finset.univ, ?_, ?_⟩
  · intro i
    rw [Finset.card_univ, Fintype.card_multiplicative, ZMod.card]
  · intro g
    exact ⟨fun _ => g, fun _ => Finset.mem_univ _, by simp [List.ofFn_succ]⟩
