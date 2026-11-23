/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.ChocolateBarNSProperty

open MetaMathlibExt

-- For the constant-one function the threshold supplied by the theorem must be zero.
example : ∃ m : ℕ, m = 0 ∧ (fun _ : ℕ ↦ 1) = (Set.Ici m).indicator (1 : ℕ → ℕ) := by
  obtain ⟨m, _, hm⟩ := (indicator_Ici_even_iff_hasNSProperty monotone_const
    (fun _ ↦ le_rfl) ⟨0, rfl⟩).mpr (hasNSProperty_const 1)
  refine ⟨m, ?_, hm⟩
  by_contra hn
  simpa [Set.indicator, hn] using congrFun hm 0

-- A positive even threshold gives a nonconstant function with the NS property.
example : HasNSProperty (fun z : ℕ ↦ if 4 ≤ z then 1 else 0) := by
  have hmono : Monotone (fun z : ℕ ↦ if 4 ≤ z then 1 else 0) := by
    intro a b hab
    dsimp only
    split_ifs <;> omega
  apply (indicator_Ici_even_iff_hasNSProperty hmono (fun z ↦ by split_ifs <;> decide)
    ⟨4, rfl⟩).mp
  exact ⟨4, ⟨2, rfl⟩, by funext z; simp [Set.indicator]⟩

-- The odd threshold three separates two inputs in the same block of length two.
example : ¬ HasNSProperty ((Set.Ici 3).indicator (1 : ℕ → ℕ)) := by
  intro hns
  have hpair := hns.2 2 3 1 (by decide) (by decide)
  simp [Set.indicator] at hpair
