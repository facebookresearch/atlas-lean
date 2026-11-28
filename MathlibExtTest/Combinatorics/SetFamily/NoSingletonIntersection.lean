/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SetFamily.NoSingletonIntersection
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card

open Finset
open MathlibExt.Combinatorics.NoSingletonIntersectionErdosProblem702Wanted

-- The strict threshold is attained by the family of all k-sets containing a fixed pair.
example {n k : ℕ} (hk : 2 ≤ k) (P : Finset (Fin n)) (hp : P.card = 2) :
    let F := (univ.powersetCard k).filter (P ⊆ ·)
    F.card = (n - 2).choose (k - 2) ∧ ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card := by
  dsimp only
  constructor
  · simpa [hp] using card_filter_powersetCard_subset P univ k (subset_univ P) (hp ▸ hk)
  · intro A ha B hb
    rw [← hp]
    exact card_le_card (subset_inter (mem_filter.mp ha).2 (mem_filter.mp hb).2)

-- The large-ground-set hypothesis is needed even for k = 4.
example :
    let F := (univ : Finset (Fin 5)).powersetCard 4
    (5 - 2).choose (4 - 2) < F.card ∧ ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).card ≠ 1 := by
  dsimp only
  constructor
  · rw [card_powersetCard, card_univ, Fintype.card_fin]
    decide
  · intro A ha B hb
    have h := card_inter_add_card_union A B
    rw [(mem_powersetCard.mp ha).2, (mem_powersetCard.mp hb).2] at h
    have hu := card_le_card (subset_univ (A ∪ B))
    rw [card_univ, Fintype.card_fin] at hu
    omega

-- Specialize the public theorem at the smallest admitted uniformity.
example : ∀ᶠ n : ℕ in Filter.atTop, ∀ F : Finset (Finset (Fin n)),
    (∀ A ∈ F, A.card = 4) → (n - 2).choose 2 < F.card →
    ∃ A ∈ F, ∃ B ∈ F, (A ∩ B).card = 1 :=
  noSingletonIntersectionBound_holds 4 (by decide)
