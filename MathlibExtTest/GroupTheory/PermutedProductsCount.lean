/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.PermutedProductsCount
import Mathlib.Data.Fintype.Perm

/-! # Tests for numbers of distinct permuted products -/

open MathlibExt.GroupTheory.PermutedProductsCountKourovka18Problem50Wanted

-- The empty family has exactly one product, the identity.
example {G : Type} [Group G] (g : Fin 0 → G) :
    (Set.range fun σ : Equiv.Perm (Fin 0) => (List.ofFn fun i => g (σ i)).prod) = {1} := by
  simp

-- Three distinct elements can give five products, forcing a collision among the six orderings.
example : ∃ (G : Type) (_ : Group G) (g : Fin 3 → G), Function.Injective g ∧
    let products := fun σ : Equiv.Perm (Fin 3) => (List.ofFn fun i => g (σ i)).prod
    (Set.range products).ncard = 5 ∧ ¬ Function.Injective products := by
  obtain ⟨G, inst, g, hg, hcard⟩ := permutedProductsTakeEveryCount_holds 3 5 (by decide) (by decide)
  refine ⟨G, inst, g, hg, hcard, fun hinj => ?_⟩
  rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_perm,
    Fintype.card_fin] at hcard
  contradiction
